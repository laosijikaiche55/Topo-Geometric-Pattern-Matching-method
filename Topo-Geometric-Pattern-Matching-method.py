import ifcopenshell
import ifcopenshell.api
import ifcopenshell.geom
import ifcopenshell.util.placement
import numpy as np
import networkx as nx
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import subprocess
import tempfile
import os
import uuid
import traceback
import datetime
import re
from scipy.spatial.transform import Rotation
from collections import Counter
import time
import threading
import sys
from functools import wraps

try:
    import psutil
except ImportError:
    psutil = None


# --- Timeout Decorator (Cross-platform) ---
class TimeoutError(Exception):
    pass


def timeout(seconds=10):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            result = [None]
            exception = [None]

            def worker():
                try:
                    result[0] = func(*args, **kwargs)
                except Exception as e:
                    exception[0] = e

            thread = threading.Thread(target=worker)
            thread.daemon = True
            thread.start()
            thread.join(seconds)

            if thread.is_alive():
                raise TimeoutError(f"Function timed out after {seconds} seconds")
            elif exception[0] is not None:
                raise exception[0]
            else:
                return result[0]

        return wrapper

    return decorator


# --- Custom Listbox with Text Wrapping ---
class WrappedListbox(tk.Frame):
    """A custom listbox-like widget that uses a Text widget to support text wrapping."""

    def __init__(self, master=None, **kwargs):
        super().__init__(master)

        self.text = tk.Text(self, wrap=tk.WORD, **kwargs)
        self.scrollbar = tk.Scrollbar(self, orient=tk.VERTICAL, command=self.text.yview)
        self.text.config(yscrollcommand=self.scrollbar.set)

        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.text.tag_configure("selected", background="#0078D7", foreground="white")
        self.text.bind("<Button-1>", self._on_click)

        # Disable editing
        self.text.config(state=tk.DISABLED)

        self._items = []
        self._selected_index = None

    def _on_click(self, event):
        """Handle clicks to select items."""
        index_str = self.text.index(f"@{event.x},{event.y}")
        line_number = int(index_str.split('.')[0])

        if line_number > 0 and line_number <= len(self._items):
            self.selection_set(line_number - 1)
            # Generate a virtual event to mimic the original Listbox's behavior
            self.event_generate("<<ListboxSelect>>")

    def insert(self, index, text):
        """Insert text like a listbox."""
        if index == tk.END:
            self._items.append(text)
            position = f"{len(self._items)}.0"
        else:
            self._items.insert(index, text)
            position = f"{index + 1}.0"

        self.text.config(state=tk.NORMAL)
        self.text.insert(position, text + '\n')
        self.text.config(state=tk.DISABLED)

    def delete(self, first, last=None):
        """Delete items like a listbox."""
        if last is None:
            last = first
        if last == tk.END:
            last = len(self._items) - 1

        first_line = first + 1
        last_line = last + 2

        self.text.config(state=tk.NORMAL)
        self.text.delete(f"{first_line}.0", f"{last_line}.0")
        self.text.config(state=tk.DISABLED)

        del self._items[first:last + 1]
        self._selected_index = None  # Clear selection after deletion

    def curselection(self):
        """Get current selection like a listbox."""
        if self._selected_index is not None:
            return (self._selected_index,)
        return ()

    def selection_set(self, index):
        """Set the selection programmatically."""
        # Remove previous selection
        self.text.tag_remove("selected", "1.0", tk.END)

        # Add new selection
        if 0 <= index < len(self._items):
            self._selected_index = index
            start = f"{index + 1}.0"
            end = f"{index + 2}.0"
            self.text.tag_add("selected", start, end)


# --- Backend Analysis Logic (Unchanged) ---
def get_element_from_port(port):
    for rel in getattr(port, 'Nests', []):
        if rel.is_a('IfcRelNests'):
            return rel.RelatingObject
    for rel in getattr(port, 'ContainedIn', []):
        if rel.is_a('IfcRelConnectsPortToElement'):
            return rel.RelatedElement
    return None


def build_connectivity_graph(ifc_file):
    G = nx.Graph()
    products = ifc_file.by_type('IfcProduct')
    for product in products:
        G.add_node(product.GlobalId, ifc_entity=product, type=product.is_a())
    port_to_element = {}
    for port in ifc_file.by_type('IfcDistributionPort'):
        element = get_element_from_port(port)
        if element:
            port_to_element[port.id()] = element.GlobalId
    for rel in ifc_file.by_type('IfcRelConnectsPorts'):
        p1, p2 = rel.RelatingPort, rel.RelatedPort
        if p1 and p2 and p1.id() in port_to_element and p2.id() in port_to_element:
            e1_id, e2_id = port_to_element[p1.id()], port_to_element[p2.id()]
            if e1_id != e2_id:
                G.add_edge(e1_id, e2_id)
    for rel in ifc_file.by_type('IfcRelConnectsElements'):
        e1, e2 = rel.RelatingElement, rel.RelatedElement
        if e1 and e2 and e1.is_a('IfcProduct') and e2.is_a('IfcProduct'):
            if e1.GlobalId != e2.GlobalId:
                G.add_edge(e1.GlobalId, e2.GlobalId)
    return G


def node_match_type(node1_attrs, node2_attrs):
    type_map = {
        'IfcPipeSegment': 'IfcFlowSegment', 'IfcDuctSegment': 'IfcFlowSegment',
        'IfcCableSegment': 'IfcFlowSegment', 'IfcDuctFitting': 'IfcFlowFitting',
        'IfcPipeFitting': 'IfcFlowFitting', 'IfcJunctionBox': 'IfcFlowFitting',
        'IfcAirTerminal': 'IfcFlowTerminal', 'IfcLightFixture': 'IfcFlowTerminal',
        'IfcSanitaryTerminal': 'IfcFlowTerminal',
    }
    t1 = type_map.get(node1_attrs['type'], node1_attrs['type'])
    t2 = type_map.get(node2_attrs['type'], node2_attrs['type'])
    return t1 == t2


def find_and_group_similar_systems(graph_to_analyze):
    systems = [graph_to_analyze.subgraph(c).copy() for c in nx.connected_components(graph_to_analyze) if len(c) >= 2]
    if not systems: return []
    groups, processed_indices = [], set()
    for i in range(len(systems)):
        if i in processed_indices: continue
        current_group = [systems[i]]
        processed_indices.add(i)
        for j in range(i + 1, len(systems)):
            if j in processed_indices: continue
            if nx.is_isomorphic(systems[i], systems[j], node_match=node_match_type):
                current_group.append(systems[j])
                processed_indices.add(j)
        groups.append(current_group)
    return [group for group in groups if len(group) > 1]


def calculate_element_obb(ifc_file, element, tolerance=0.001):
    try:
        settings = ifcopenshell.geom.settings()
        settings.set(settings.USE_WORLD_COORDS, True)
        shape = ifcopenshell.geom.create_shape(settings, element)
        if shape:
            verts = np.array(shape.geometry.verts).reshape(-1, 3)
            if len(verts) == 0: return None
            center = np.mean(verts, axis=0)
            centered_vertices = verts - center
            if len(centered_vertices) < 2:
                return {'center': center, 'extents': np.array([tolerance, tolerance, tolerance]), 'rotation': np.eye(3)}
            cov_matrix = np.cov(centered_vertices, rowvar=False)
            eigenvalues, eigenvectors = np.linalg.eigh(cov_matrix)
            sorted_indices = np.argsort(eigenvalues)[::-1]
            eigenvectors = eigenvectors[:, sorted_indices]
            if np.linalg.det(eigenvectors) < 0: eigenvectors[:, 2] = -eigenvectors[:, 2]
            rotation_matrix = eigenvectors
            local_vertices = np.dot(centered_vertices, rotation_matrix)
            min_vals, max_vals = np.min(local_vertices, axis=0), np.max(local_vertices, axis=0)
            extents = np.maximum(max_vals - min_vals, tolerance)
            obb_center = center + np.dot((min_vals + max_vals) / 2, rotation_matrix.T)
            return {'center': obb_center, 'extents': extents, 'rotation': rotation_matrix}
        return None
    except Exception as e:
        print(f"Error calculating element OBB: {e}")
        return None


SYMMETRY_TRANSFORMS = [np.array([[s1, 0, 0], [0, s2, 0], [0, 0, s3]]) for s1 in [1, -1] for s2 in [1, -1] for s3 in
                       [1, -1]]


def calculate_obb_similarity_with_symmetries(obb1, obb2, size_weight=1.0, angle_weight=0.0, angle_tolerance_deg=15.0):
    if obb1 is None or obb2 is None: return 0.0
    sorted_extents1 = np.sort(obb1['extents'])
    sorted_extents2 = np.sort(obb2['extents'])
    size_diff = np.abs(sorted_extents1 - sorted_extents2)
    max_extents = np.maximum(sorted_extents1, sorted_extents2)
    max_extents[max_extents < 1e-6] = 1.0
    size_similarity = 1.0 - np.mean(size_diff / max_extents)
    if angle_weight > 0:
        r1, r2 = obb1['rotation'], obb2['rotation']
        min_angle_deg = 360.0
        for transform in SYMMETRY_TRANSFORMS:
            r2_transformed = np.dot(r2, transform)
            relative_rotation = np.dot(r1.T, r2_transformed)
            trace = np.clip(np.trace(relative_rotation), -1.0, 3.0)
            angle_rad = np.arccos((trace - 1.0) / 2.0)
            angle_deg = np.degrees(angle_rad)
            angle_deg = min(angle_deg, 180.0 - angle_deg)
            if angle_deg < min_angle_deg: min_angle_deg = angle_deg
        angle_similarity = max(0.0, 1.0 - (min_angle_deg / angle_tolerance_deg))
    else:
        angle_similarity = 1.0
    return (size_weight * size_similarity + angle_weight * angle_similarity) / (size_weight + angle_weight) if (
                                                                                                                           size_weight + angle_weight) > 0 else 0


def refine_groups_with_geometric_fingerprint(ifc_file, groups, original_metadata, similarity_threshold=0.8):
    refined_groups, refined_metadata = [], []
    all_systems = [system for group in groups for system in group]
    element_obb_cache = {}
    print("Pre-calculating component OBBs for geometric fingerprint analysis...")
    for system_graph in all_systems:
        for guid in system_graph.nodes():
            if guid not in element_obb_cache:
                element = ifc_file.by_guid(guid)
                if element: element_obb_cache[guid] = calculate_element_obb(ifc_file, element)
    print("OBB pre-calculation complete.")
    for group_idx, group in enumerate(groups):
        if len(group) < 2:
            if len(group) > 0:
                refined_groups.append(group)
                refined_metadata.append(original_metadata[group_idx])
            continue
        sub_groups, processed_indices = [], set()
        for i in range(len(group)):
            if i in processed_indices: continue
            new_sub_group = [group[i]]
            processed_indices.add(i)
            for j in range(i + 1, len(group)):
                if j in processed_indices: continue
                if not nx.is_isomorphic(group[i], group[j], node_match=node_match_type): continue
                matcher_ij = nx.isomorphism.GraphMatcher(group[i], group[j], node_match=node_match_type)
                if not matcher_ij.is_isomorphic(): continue
                mapping = next(matcher_ij.isomorphisms_iter())
                total_sim, pair_count = 0.0, 0
                for node_i_guid, node_j_guid in mapping.items():
                    obb_i, obb_j = element_obb_cache.get(node_i_guid), element_obb_cache.get(node_j_guid)
                    if obb_i and obb_j:
                        sim = calculate_obb_similarity_with_symmetries(obb_i, obb_j, size_weight=1.0, angle_weight=0.0)
                        total_sim += sim
                        pair_count += 1
                if pair_count > 0 and (total_sim / pair_count) >= similarity_threshold:
                    new_sub_group.append(group[j])
                    processed_indices.add(j)
            if len(new_sub_group) > 1: sub_groups.append(new_sub_group)
        for sub_group in sub_groups:
            refined_groups.append(sub_group)
            refined_metadata.append(original_metadata[group_idx].copy())
    return refined_groups, refined_metadata


# --- Graphical User Interface ---
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("IFC Similar Structure Analysis and System Creation Tool")
        self.geometry("1280x850")
        self.ifc_file_instance = None
        self.original_path = None
        self.similar_groups, self.group_metadata, self.pattern_graphs = [], [], []
        self.system_names = {}
        self.viewer_path = "E:\\BIM Vision\\BIM_Vision_x64.exe"
        self.use_obb_refinement = tk.BooleanVar(value=True)
        self.use_element_obb_verification = tk.BooleanVar(value=True)
        self.total_components, self.mep_components, self.spatial_components = 0, 0, 0
        self.ifc_schema = None
        self.obb_cache = {}
        self.element_obb_similarity_threshold = tk.DoubleVar(value=0.7)

        # --- MODIFICATION START: Variables for sliders ---
        self.node_size_var = tk.IntVar(value=2500)
        self.font_size_var = tk.IntVar(value=7)
        # --- MODIFICATION END ---

        top_panel_container = tk.Frame(self, bd=2, relief=tk.RIDGE)
        top_panel_container.pack(side=tk.TOP, fill=tk.X, padx=5, pady=(5, 0))
        top_row_frame = tk.Frame(top_panel_container)
        top_row_frame.pack(fill=tk.X, padx=5, pady=2)
        tk.Button(top_row_frame, text="1. Select Main IFC File", command=self.load_ifc).pack(side=tk.LEFT, padx=(0, 10))
        self.import_pattern_button = tk.Button(top_row_frame, text="2. Import External Pattern IFC",
                                               command=self.import_external_ifc, state=tk.DISABLED)
        self.import_pattern_button.pack(side=tk.LEFT, padx=(0, 10))
        self.analyze_button = tk.Button(top_row_frame, text="3. Analyze Similar Structures", command=self.analyze,
                                        state=tk.DISABLED)
        self.analyze_button.pack(side=tk.LEFT, padx=(0, 10))
        self.file_label = tk.Label(top_row_frame, text="No file selected")
        self.file_label.pack(side=tk.RIGHT, padx=10)
        bottom_row_frame = tk.Frame(top_panel_container)
        bottom_row_frame.pack(fill=tk.X, padx=5, pady=2)
        tk.Checkbutton(bottom_row_frame, text="Enable Geometric Fingerprint Refinement",
                       variable=self.use_obb_refinement).pack(side=tk.LEFT, padx=(0, 10))
        tk.Checkbutton(bottom_row_frame, text="Enable Element-level OBB Verification",
                       variable=self.use_element_obb_verification).pack(side=tk.LEFT, padx=(0, 10))
        obb_threshold_frame = tk.Frame(bottom_row_frame)
        obb_threshold_frame.pack(side=tk.LEFT, padx=(0, 10))
        tk.Label(obb_threshold_frame, text="Element OBB Threshold:").pack(side=tk.LEFT)
        tk.Entry(obb_threshold_frame, textvariable=self.element_obb_similarity_threshold, width=5).pack(side=tk.LEFT)

        paned_window = tk.PanedWindow(self, orient=tk.HORIZONTAL, sashrelief=tk.RAISED, bd=2)
        paned_window.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=5, pady=5)

        list_frame = tk.Frame(paned_window, bd=1, relief=tk.GROOVE)
        tk.Label(list_frame, text="Analysis Result Groups").pack(fill=tk.X)
        self.results_listbox = WrappedListbox(list_frame, font=("Segoe UI", 9), borderwidth=0, highlightthickness=0)
        self.results_listbox.pack(fill=tk.BOTH, expand=True)
        self.results_listbox.bind('<<ListboxSelect>>', self.on_group_select)
        paned_window.add(list_frame, stretch="never")

        self.canvas_frame = tk.Frame(paned_window, bd=1, relief=tk.GROOVE)
        self.fig = Figure(figsize=(8, 6), dpi=100)
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.canvas_frame)

        # --- MODIFICATION START: Add sliders below the canvas ---
        self.canvas.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        graph_controls_frame = tk.Frame(self.canvas_frame)
        graph_controls_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=5)

        node_slider = tk.Scale(graph_controls_frame, from_=500, to=5000, orient=tk.HORIZONTAL,
                               label="Node Size", variable=self.node_size_var, command=self._on_slider_change)
        node_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)

        font_slider = tk.Scale(graph_controls_frame, from_=3, to=15, orient=tk.HORIZONTAL,
                               label="Font Size", variable=self.font_size_var, command=self._on_slider_change)
        font_slider.pack(side=tk.LEFT, fill=tk.X, expand=True)
        # --- MODIFICATION END ---

        self.ax.text(0.5, 0.5, "Select a group to display its structure diagram", ha='center', va='center')
        self.canvas.draw()
        paned_window.add(self.canvas_frame, stretch="always")

        bottom_container = tk.Frame(self)
        bottom_container.pack(side=tk.BOTTOM, fill=tk.X, padx=0, pady=0)
        bottom_frame = tk.Frame(bottom_container, bd=2, relief=tk.RIDGE)
        bottom_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)
        tk.Label(bottom_frame, text="New System Base Name:").pack(side=tk.LEFT, padx=5)
        self.rename_entry = tk.Entry(bottom_frame, width=40)
        self.rename_entry.pack(side=tk.LEFT, padx=5)
        self.rename_button = tk.Button(bottom_frame, text="Set/Update System Name",
                                       command=self.set_system_name_for_group, state=tk.DISABLED)
        self.rename_button.pack(side=tk.LEFT, padx=5, pady=5)
        self.show_3d_button = tk.Button(bottom_frame, text="Show in 3D Viewer", command=self.show_in_viewer,
                                        state=tk.DISABLED)
        self.show_3d_button.pack(side=tk.LEFT, padx=5, pady=5)
        self.save_button = tk.Button(bottom_frame, text="Generate and Save...", command=self.generate_and_save_ifc,
                                     state=tk.DISABLED)
        self.save_button.pack(side=tk.RIGHT, padx=5, pady=5)
        status_frame = tk.Frame(bottom_container, bd=1, relief=tk.SUNKEN)
        status_frame.pack(side=tk.TOP, fill=tk.X)
        self.status_label = tk.Label(status_frame, text="Please load an IFC file to begin...", anchor='w')
        self.status_label.pack(side=tk.LEFT, padx=5, pady=2)

        self.current_graph, self.graph_pos, self._dragged_node = None, None, None
        self.canvas.mpl_connect('button_press_event', self.on_press)
        self.canvas.mpl_connect('button_release_event', self.on_release)
        self.canvas.mpl_connect('motion_notify_event', self.on_motion)

    # --- MODIFICATION START: New method to handle slider changes ---
    def _on_slider_change(self, value):
        """Redraws the graph when a slider is moved."""
        if self.current_graph:
            self.redraw_graph()

    # --- MODIFICATION END ---

    def _update_status(self, text):
        self.status_label.config(text=text)
        self.update_idletasks()

    def load_ifc(self):
        path = filedialog.askopenfilename(title="Select Main IFC File",
                                          filetypes=[("IFC files", "*.ifc"), ("All files", "*.*")])
        if not path: return
        try:
            self._update_status(f"Loading file: {os.path.basename(path)}...")
            self.original_path = path
            self.ifc_file_instance = ifcopenshell.open(self.original_path)
            self.ifc_schema = self.ifc_file_instance.schema
            self.obb_cache, self.system_names, self.similar_groups, self.group_metadata, self.pattern_graphs = {}, {}, [], [], []
            all_products = self.ifc_file_instance.by_type('IfcProduct')
            self.total_components = len(all_products)
            mep_types = ['IfcFlowSegment', 'IfcFlowFitting', 'IfcFlowTerminal', 'IfcFlowController', 'IfcFlowStorage',
                         'IfcFlowTreatmentDevice', 'IfcEnergyConversionDevice', 'IfcDistributionFlowElement',
                         'IfcDistributionChamberElement', 'IfcDistributionElement']
            spatial_types = ['IfcSite', 'IfcBuilding', 'IfcBuildingStorey', 'IfcSpace']
            self.mep_components = sum(1 for p in all_products if p.is_a() in mep_types)
            self.spatial_components = sum(1 for p in all_products if p.is_a() in spatial_types)
            self.file_label.config(text=f"Main file loaded: {os.path.basename(self.original_path)} ({self.ifc_schema})")
            self.analyze_button.config(state=tk.NORMAL)
            self.import_pattern_button.config(state=tk.NORMAL)
            self.results_listbox.delete(0, tk.END)
            self.ax.clear()
            self.ax.text(0.5, 0.5, "Click 'Analyze' or 'Import Pattern'", ha='center', va='center')
            self.canvas.draw()
            self.rename_entry.delete(0, tk.END)
            self.rename_button.config(state=tk.DISABLED)
            self.save_button.config(state=tk.DISABLED)
            self.show_3d_button.config(state=tk.DISABLED)
            self.current_graph, self.graph_pos, self._dragged_node = None, None, None
            self._update_status(
                f"File loaded successfully | Total Components: {self.total_components} | MEP Components: {self.mep_components} | Spatial Elements: {self.spatial_components}")
        except Exception as e:
            self._update_status("File loading failed!")
            messagebox.showerror("Loading Error", f"Could not load or parse IFC file: {e}")

    def import_external_ifc(self):
        if not self.ifc_file_instance:
            messagebox.showwarning("Invalid Operation", "Please load the main IFC file first.")
            return
        path = filedialog.askopenfilename(title="Select external IFC file containing pattern systems",
                                          filetypes=[("IFC files", "*.ifc")])
        if not path: return
        try:
            external_ifc = ifcopenshell.open(path)
            G_external = build_connectivity_graph(external_ifc)
            systems = [G_external.subgraph(c).copy() for c in nx.connected_components(G_external) if len(c) >= 2]
            if not systems:
                messagebox.showinfo("Information",
                                    "No systems (component count >= 2) suitable as patterns were found in the external file.")
                return
            self.pattern_graphs = systems
            pattern_filename = os.path.basename(path)
            for i, p_graph in enumerate(self.pattern_graphs):
                p_graph.name = f"{pattern_filename} (System {i + 1})"
                p_graph.element_obbs = {}
                for guid, data in p_graph.nodes(data=True):
                    if 'ifc_entity' not in data:
                        data['ifc_entity'] = type('FakeEntity', (object,),
                                                  {'is_a': lambda: data['type'], 'Name': "Pattern Node"})()
                    element = external_ifc.by_guid(guid)
                    if element: p_graph.element_obbs[guid] = calculate_element_obb(external_ifc, element)
            messagebox.showinfo("Pattern Loaded Successfully",
                                f"Loaded {len(self.pattern_graphs)} systems as search patterns from {pattern_filename}.\nPlease now click '3. Analyze Similar Structures' to find matches in the main model.")
            self.file_label.config(
                text=f"Main File: {os.path.basename(self.original_path)} | Pattern: {pattern_filename}")
        except Exception as e:
            messagebox.showerror("Import Error", f"An error occurred while importing the external pattern file: {e}")
            traceback.print_exc()

    def verify_element_obb_match(self, main_element_entity, pattern_element_guid, pattern_graph):
        if not self.use_element_obb_verification.get(): return True
        main_element_guid = main_element_entity.GlobalId
        main_obb = self.obb_cache.get(main_element_guid)
        if not main_obb:
            main_obb = calculate_element_obb(self.ifc_file_instance, main_element_entity)
            self.obb_cache[main_element_guid] = main_obb
        pattern_obb = pattern_graph.element_obbs.get(pattern_element_guid)
        if main_obb is None or pattern_obb is None: return True
        similarity = calculate_obb_similarity_with_symmetries(main_obb, pattern_obb, size_weight=1.0, angle_weight=0.0)
        return similarity >= self.element_obb_similarity_threshold.get()

    def verify_system_geometry_match(self, mapping, pattern_graph, main_component_graph):
        if not self.use_element_obb_verification.get(): return True
        for main_guid, pattern_guid in mapping.items():
            main_element_entity = main_component_graph.nodes[main_guid]['ifc_entity']
            if not self.verify_element_obb_match(main_element_entity, pattern_guid, pattern_graph): return False
        return True

    def analyze(self):
        if not self.ifc_file_instance: return
        start_time = time.time()
        self._update_status("Building main connectivity graph, please wait...")
        try:
            self.similar_groups, self.group_metadata = [], []
            self.results_listbox.delete(0, tk.END)
            main_graph = build_connectivity_graph(self.ifc_file_instance)
            total_nodes, total_edges = main_graph.number_of_nodes(), main_graph.number_of_edges()
            self._update_status(
                f"Main graph: {total_nodes} nodes, {total_edges} connections | Analyzing for similarity...")
            occupied_nodes = set()
            if self.pattern_graphs:
                for p_graph in self.pattern_graphs:
                    print(
                        f"Matching pattern: {p_graph.name} | Nodes: {p_graph.number_of_nodes()} | Edges: {p_graph.number_of_edges()}")
                    current_group = []
                    for comp in nx.connected_components(main_graph):
                        component_graph = main_graph.subgraph(comp).copy()
                        pattern_types = Counter(data['type'] for _, data in p_graph.nodes(data=True))
                        comp_types = Counter(data['type'] for _, data in component_graph.nodes(data=True))
                        if not all(comp_types.get(t, 0) >= count for t, count in pattern_types.items()): continue
                        if (
                                component_graph.number_of_nodes() < p_graph.number_of_nodes() or component_graph.number_of_edges() < p_graph.number_of_edges()): continue
                        GM = nx.isomorphism.GraphMatcher(component_graph, p_graph, node_match=node_match_type)
                        try:
                            matches = timeout(30)(lambda: list(GM.subgraph_isomorphisms_iter()))()
                        except TimeoutError as te:
                            print(f"  Matching timed out, skipping large component: {te}")
                            continue
                        except Exception as e:
                            print(f"  An error occurred during matching: {e}")
                            continue
                        for mapping in matches:
                            matched_guids = set(mapping.keys())
                            if occupied_nodes & matched_guids: continue
                            if not self.verify_system_geometry_match(mapping, p_graph, component_graph):
                                print("  Geometric verification failed, skipping this match.")
                                continue
                            occupied_nodes |= matched_guids
                            subgraph = component_graph.subgraph(matched_guids).copy()
                            current_group.append(subgraph)
                            print(f"  Found matching system, size: {subgraph.number_of_nodes()} nodes")
                    if current_group:
                        self.similar_groups.append(current_group)
                        self.group_metadata.append(
                            {'type': 'External Match', 'pattern_name': p_graph.name, 'representative': p_graph})
                        print(f"  Matched {len(current_group)} systems")
            remaining_nodes = set(main_graph.nodes()) - occupied_nodes
            if remaining_nodes:
                print(f"Remaining nodes for internal analysis: {len(remaining_nodes)}")
                remaining_graph = main_graph.subgraph(remaining_nodes).copy()
                internal_groups = find_and_group_similar_systems(remaining_graph)
                self.similar_groups.extend(internal_groups)
                for group in internal_groups: self.group_metadata.append({'type': 'Internal Similarity'})
                print(f"Found {len(internal_groups)} internal similarity groups")
            if self.use_obb_refinement.get() and self.similar_groups:
                messagebox.showinfo("Geometric Fingerprint Refinement",
                                    "Using geometric fingerprint for secondary confirmation and refinement, this may take some time...")
                self._update_status(
                    f"Main graph: {total_nodes} nodes, {total_edges} edges | Performing geometric fingerprint refinement...")
                try:
                    self.similar_groups, self.group_metadata = refine_groups_with_geometric_fingerprint(
                        self.ifc_file_instance, self.similar_groups, self.group_metadata, similarity_threshold=0.8)
                    messagebox.showinfo("Refinement Complete",
                                        "Geometric fingerprint secondary confirmation and refinement is complete!")
                except Exception as e:
                    messagebox.showerror("Refinement Error", f"An error occurred during refinement: {e}")
                    traceback.print_exc()
            if not self.similar_groups:
                self.results_listbox.insert(tk.END, "No matching or similar structure groups were found.")
                messagebox.showinfo("Analysis Complete", "No matching or similar structure groups were found.")
            else:
                for i, group in enumerate(self.similar_groups):
                    metadata = self.group_metadata[i]
                    group_type = metadata['type']
                    if group_type == 'External Match':
                        listbox_text = f"Group {i + 1} (Matching '{metadata['pattern_name']}'): {len(group)} systems"
                    else:
                        listbox_text = f"Group {i + 1} (Internal Similarity): {len(group)} systems ({group[0].number_of_nodes()} components)"
                    self.results_listbox.insert(tk.END, listbox_text)
                messagebox.showinfo("Analysis Complete",
                                    f"Analysis finished! Found {len(self.similar_groups)} result groups.")
            duration = time.time() - start_time
            mem_usage_text = f" | Memory: {psutil.Process(os.getpid()).memory_info().rss / (1024 * 1024):.2f} MB" if psutil else ""
            self._update_status(
                f"Analysis complete | Main graph: {total_nodes} nodes, {total_edges} edges | Time: {duration:.2f}s{mem_usage_text}")
            self.save_button.config(state=tk.NORMAL)
        except Exception as e:
            duration = time.time() - start_time
            self._update_status(f"Analysis failed! Time: {duration:.2f}s. Error: {e}")
            messagebox.showerror("Analysis Error", f"An error occurred during analysis: {e}")
            traceback.print_exc()

    def on_press(self, event):
        if event.inaxes != self.ax or self.graph_pos is None: return
        min_dist_sq, closest_node = float('inf'), None
        for node, pos in self.graph_pos.items():
            dist_sq = (pos[0] - event.xdata) ** 2 + (pos[1] - event.ydata) ** 2
            if dist_sq < min_dist_sq: min_dist_sq, closest_node = dist_sq, node
        if min_dist_sq < 0.01: self._dragged_node = closest_node

    def on_motion(self, event):
        if self._dragged_node is None or event.inaxes != self.ax: return
        self.graph_pos[self._dragged_node] = (event.xdata, event.ydata)
        self.redraw_graph()

    def on_release(self, event):
        self._dragged_node = None
        self.canvas.draw_idle()

    def redraw_graph(self):
        if self.current_graph is None or self.graph_pos is None: return
        self.ax.clear()

        selection = self.results_listbox.curselection()
        if not selection: return

        metadata = self.group_metadata[selection[0]]
        title = f"Pattern for Group {selection[0] + 1}: '{metadata['pattern_name']}'" if metadata[
                                                                                             'type'] == 'External Match' else f"Structure Diagram for Group {selection[0] + 1} (Internal Similarity)"
        self.ax.set_title(title)

        color_map = {'IfcFlowSegment': 'skyblue', 'IfcDuctSegment': 'skyblue', 'IfcPipeSegment': 'skyblue',
                     'IfcFlowFitting': 'tomato', 'IfcDuctFitting': 'tomato', 'IfcPipeFitting': 'tomato',
                     'IfcFlowTerminal': 'gold', 'IfcAirTerminal': 'gold', 'IfcFlowController': 'lightgreen',
                     'IfcEnergyConversionDevice': 'pink', 'IfcDistributionFlowElement': 'lightblue'}
        node_colors = [color_map.get(data['type'], 'lightgrey') for _, data in self.current_graph.nodes(data=True)]

        # --- MODIFICATION: Use slider variables for sizes ---
        nx.draw(self.current_graph, ax=self.ax, pos=self.graph_pos, with_labels=False,
                node_color=node_colors, node_size=self.node_size_var.get(), width=1.5)

        labels = {node: f"{data['ifc_entity'].is_a().replace('Ifc', '')}\n{data['ifc_entity'].Name or '未命名'}" for
                  node, data in self.current_graph.nodes(data=True)}

        nx.draw_networkx_labels(self.current_graph, self.graph_pos, labels,
                                font_size=self.font_size_var.get(), ax=self.ax)
        # --- MODIFICATION END ---

        self.canvas.draw_idle()

    def on_group_select(self, event):
        selection = self.results_listbox.curselection()
        if not selection or not self.similar_groups: return
        group_index = selection[0]
        if group_index >= len(self.similar_groups): return
        metadata = self.group_metadata[group_index]
        self.rename_button.config(state=tk.NORMAL)
        self.show_3d_button.config(state=tk.NORMAL)
        self.rename_entry.delete(0, tk.END)
        self.rename_entry.insert(0, self.system_names.get(group_index, ""))
        self._dragged_node = None
        representative_graph = metadata.get('representative', self.similar_groups[group_index][0])
        self.current_graph = representative_graph
        self.graph_pos = nx.spring_layout(self.current_graph, seed=42)
        self.redraw_graph()

    def set_system_name_for_group(self):
        selection = self.results_listbox.curselection()
        if not selection:
            messagebox.showwarning("Invalid Operation", "Please select a group from the list on the left.")
            return
        base_name = self.rename_entry.get().strip()
        if not base_name:
            messagebox.showwarning("Invalid Operation", "Please enter a base name for the system.")
            return
        group_index = selection[0]
        self.system_names[group_index] = base_name
        metadata = self.group_metadata[group_index]
        listbox_text = f"Group {group_index + 1} (Matching '{metadata['pattern_name']}'): {len(self.similar_groups[group_index])} systems -> Name: {base_name}" if \
        metadata[
            'type'] == 'External Match' else f"Group {group_index + 1} (Internal Similarity): {len(self.similar_groups[group_index])} systems ({self.similar_groups[group_index][0].number_of_nodes()} components) -> Name: {base_name}"
        self.results_listbox.delete(group_index)
        self.results_listbox.insert(group_index, listbox_text)
        self.results_listbox.selection_set(group_index)
        self.save_button.config(state=tk.NORMAL)
        messagebox.showinfo("Name Set",
                            f"The base name for Group {group_index + 1} has been set to '{base_name}'.\nAfter setting all desired names, click 'Generate and Save...'.")

    def generate_and_save_ifc(self):
        if not self.system_names:
            messagebox.showinfo("No Changes",
                                "No system names have been set. Please set a name for at least one group.")
            return
        save_path = filedialog.asksaveasfilename(title="Save IFC file with new systems", defaultextension=".ifc",
                                                 filetypes=[("IFC files", "*.ifc")])
        if not save_path: return
        temp_ifc_path = None
        try:
            self._update_status(f"Creating systems and preparing to save to {os.path.basename(save_path)}...")
            print("Creating a temporary copy of the IFC file for modification...")
            fd, temp_ifc_path = tempfile.mkstemp(suffix=".ifc")
            os.close(fd)
            self.ifc_file_instance.write(temp_ifc_path)
            modified_ifc_file = ifcopenshell.open(temp_ifc_path)
            if modified_ifc_file is None: raise ValueError("Failed to create IFC copy from temp file, cannot continue.")
            print("Temporary copy created successfully.")
            print(f"Preparing to create systems for {len(self.system_names)} groups...")
            owner_history = ifcopenshell.api.run("owner.create_owner_history", modified_ifc_file)
            for group_index, base_name in self.system_names.items():
                selected_group = self.similar_groups[group_index]
                print(
                    f"  Processing Group {group_index + 1} ('{base_name}'), containing {len(selected_group)} sub-systems.")
                for i, system_graph in enumerate(selected_group):
                    new_system = modified_ifc_file.create_entity("IfcSystem", Name=f"{base_name}-{i + 1}")
                    elements_in_system = [elem for elem in
                                          (modified_ifc_file.by_guid(guid) for guid in system_graph.nodes()) if elem]
                    if not elements_in_system:
                        print(f"    Warning: No components found in the copy for system '{new_system.Name}'.")
                        continue
                    modified_ifc_file.create_entity("IfcRelAssignsToGroup", ifcopenshell.guid.new(), owner_history,
                                                    RelatedObjects=elements_in_system, RelatingGroup=new_system)
                    print(
                        f"    -> Created system '{new_system.Name}' and associated {len(elements_in_system)} components.")
            print(f"All systems created, writing to file: {save_path}")
            modified_ifc_file.write(save_path)
            messagebox.showinfo("Save Successful",
                                f"The file with new systems has been saved successfully to:\n{save_path}")
            self._update_status(
                f"File saved successfully | Total Components: {self.total_components} | MEP Components: {self.mep_components}")
            self.system_names = {}
            self.save_button.config(state=tk.DISABLED)
        except Exception as e:
            self._update_status(f"Error saving file: {e}")
            messagebox.showerror("Save Failed", f"A critical error occurred during file generation or saving: {e}")
            traceback.print_exc()
        finally:
            if temp_ifc_path and os.path.exists(temp_ifc_path):
                try:
                    os.remove(temp_ifc_path)
                    print(f"Deleted temporary file: {temp_ifc_path}")
                except Exception as e:
                    print(f"Warning: Failed to delete temporary file: {e}")

    def _create_temp_ifc_for_group(self, guids):
        if not guids: return None
        temp_file = ifcopenshell.file(schema=self.ifc_file_instance.schema)
        element_map = {e.id(): temp_file.add(e) for e in (self.ifc_file_instance.by_guid(guid) for guid in guids) if e}
        all_related_rels = set()
        for element_id in element_map:
            element = self.ifc_file_instance[element_id]
            for rel in getattr(element, 'HasPorts', []):
                if not rel.is_a('IfcRelNests'): continue
                for port in rel.RelatedObjects:
                    all_related_rels.update(getattr(port, 'ConnectedFrom', []))
                    all_related_rels.update(getattr(port, 'ConnectedTo', []))
        for rel in all_related_rels:
            e1, e2 = get_element_from_port(rel.RelatingPort), get_element_from_port(rel.RelatedPort)
            if e1 and e2 and e1.GlobalId in guids and e2.GlobalId in guids: temp_file.add(rel)
        owner_history = ifcopenshell.api.run("owner.create_owner_history", temp_file)
        project = temp_file.createIfcProject(OwnerHistory=owner_history)
        temp_file.createIfcRelAggregates(ifcopenshell.guid.new(), owner_history, RelatingObject=project,
                                         RelatedObjects=list(element_map.values()))
        temp_path = os.path.join(tempfile.gettempdir(), f"ifc_group_preview_{uuid.uuid4().hex}.ifc")
        temp_file.write(temp_path)
        return temp_path

    def show_in_viewer(self):
        selection = self.results_listbox.curselection()
        if not selection:
            messagebox.showwarning("Invalid Operation", "Please select a group from the list on the left.")
            return
        if not os.path.exists(self.viewer_path):
            messagebox.showerror("Configuration Error",
                                 f"IFC viewer not found. Please configure the correct path in the script:\n{self.viewer_path}")
            return
        group_index = selection[0]
        if group_index >= len(self.similar_groups): return
        guids_to_show = list(self.similar_groups[group_index][0].nodes())
        element_count = len(guids_to_show)
        if element_count > 100 and not messagebox.askyesno("Large Group Warning",
                                                           f"This group contains {element_count} elements. Creating the temporary file and launching the viewer might be slow.\nDo you want to continue?"):
            return
        try:
            self._update_status(f"Creating temporary file for 3D preview ({element_count} components)...")
            temp_ifc_path = self._create_temp_ifc_for_group(guids_to_show)
            if not temp_ifc_path: raise ValueError("Failed to create temp file, no valid GUIDs.")
            print(
                f"Generated temporary IFC file: {temp_ifc_path} | Size: {os.path.getsize(temp_ifc_path) / 1024:.2f} KB")
            subprocess.Popen([self.viewer_path, os.path.abspath(temp_ifc_path)])
            self._update_status("Launched 3D viewer for preview.")
            messagebox.showinfo("Opening Viewer",
                                f"A temporary IFC file has been created for the representative system of the selected group and is being opened in the viewer.\nFile location: {temp_ifc_path}\nThis file can be automatically cleaned up on system restart.")
        except Exception as e:
            error_msg = f"An error occurred while creating the temporary IFC or launching the viewer: {e}"
            self._update_status("3D preview failed!")
            traceback.print_exc()
            messagebox.showerror("Viewer Launch Failed", error_msg)


if __name__ == "__main__":
    try:
        plt.rcParams['font.sans-serif'] = ['SimHei', 'Microsoft YaHei']
        plt.rcParams['axes.unicode_minus'] = False
    except Exception as e:
        print(f"Warning: Failed to set Chinese font ({e}). Chinese characters in the plot may not display correctly.")
    app = App()
    app.mainloop()