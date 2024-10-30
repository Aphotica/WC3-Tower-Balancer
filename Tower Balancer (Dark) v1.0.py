import customtkinter as ctk
from tkinter import filedialog, messagebox, Text
import tkinter as tk
import pandas as pd
import numpy as np
import math
import threading
import logging
from scipy import stats  # Added for Z-Score and Percent Rank calculations


## Color locator:
    ## Backgrounds: General (#333333), Click Focus (#7abdf5), Hover Focus (#6897bb), Result Window (#2E2E2E / #151924)
    ## Text: Result Header (#00FFFF), Outlier Analysis (#FFFF00), Outlier Tower (#00CED1), Outlier Balance Range Reference (#00FF00), Tower Header Highlight (#FFC107)

# Calculation function code as a string
calculate_dps_per_gold_code = '''
def calculate_dps_per_gold(base_damage, dice, sides_per_die, cooldown, range_val,
                           full_splash, medium_splash, small_splash, gold_cost,
                           spell_dps=0, spell_dps_cooldown=1, poison=False,
                           utility_boost=1.0, slow_percentage=0, poison_duration=1,
                           slow_duration=3, enemy_speed=415, target_type='All',
                           include_splash=True):
    import math

    # Calculate average damage per hit
    avg_damage = base_damage + (dice * (sides_per_die + 1) / 2)

    # Calculate hits per second
    hits_per_second = 1 / cooldown

    # Calculate base DPS (damage per second)
    base_dps = avg_damage * hits_per_second

    # Polynomial Range Modifier
    def polynomial_range_modifier(range_val, n=0.6, max_range=2800):
        normalized_range = (range_val - 200) / (max_range - 200)
        normalized_range = max(0, min(normalized_range, 1))  # Ensure within [0,1]
        return 1 + normalized_range ** n

    range_adjustment = polynomial_range_modifier(range_val)

    range_adjusted_dps = base_dps * range_adjustment

    # Adjusted Splash Multiplier
    splash_multiplier = 1.2

    # Calculate splash DPS if included
    if include_splash:
        total_splash_dps = (
            (full_splash / 100 * range_adjusted_dps) +
            (medium_splash / 100 * range_adjusted_dps * 0.5) +
            (small_splash / 100 * range_adjusted_dps * 0.25)
        ) * splash_multiplier
    else:
        total_splash_dps = 0

    # Add Spell DPS (if provided)
    if spell_dps and spell_dps_cooldown > 0:
        special_dps = spell_dps / spell_dps_cooldown
    else:
        special_dps = 0

    # Adjusted Poison Effect
    if poison:
        poison_dps = 5  # 5 DPS for poison
        total_poison_damage = poison_dps * poison_duration
        poison_dps_contribution = total_poison_damage / poison_duration
        special_dps += poison_dps_contribution

        # Calculate additional hits due to slow effect from poison
        effective_speed = enemy_speed * (1 - 0.3)  # Poison slows by 30%
        # Calculate extra time in range due to slow
        slow_factor = 1 / (1 - 0.3)  # ~1.4286
        extra_time_poison = slow_duration * (slow_factor - 1)
        additional_hits_poison = extra_time_poison * hits_per_second
        special_dps += (additional_hits_poison * avg_damage) / slow_duration

    # Enhanced Slow Effect
    if slow_percentage > 0:
        effective_speed = enemy_speed * (1 - slow_percentage / 100)
        # Avoid division by zero or negative speed
        if effective_speed <= 0:
            effective_speed = 1  # Or handle as complete immobilization

        # Calculate the factor by which slow increases time in range
        slow_factor = 1 / (1 - slow_percentage / 100)

        # Extra time exposed due to slow
        extra_time = slow_duration * (slow_factor - 1)

        # Additional hits during the extra time
        additional_hits = extra_time * hits_per_second

        # Additional damage per second from the slow
        slow_dps_contribution = (additional_hits * avg_damage) / slow_duration
    else:
        slow_dps_contribution = 0

    total_dps = range_adjusted_dps + total_splash_dps + special_dps + slow_dps_contribution

    # Apply utility boost
    total_dps *= utility_boost

    # Calculate DPS per Gold using linear scaling
    dps_per_gold = (total_dps / gold_cost) * 100

    return total_dps, dps_per_gold
'''

class Tooltip(object):
    def __init__(self, widget, text='widget info'):
        self.waittime = 2000     # milliseconds
        self.wraplength = 250   # pixels
        self.widget = widget
        self.text = text
        self.widget.bind("<Enter>", self.enter)
        self.widget.bind("<Leave>", self.leave)
        self.widget.bind("<ButtonPress>", self.leave)
        self.id = None
        self.tw = None
        self.result_labels = []

    def enter(self, event=None):
        self.schedule()
    def leave(self, event=None):
        self.unschedule()
        self.hidetip()
    def schedule(self):
        self.unschedule()
        self.id = self.widget.after(self.waittime, self.showtip)
    def unschedule(self):
        id = self.id
        self.id = None
        if id:
            self.widget.after_cancel(id)
    def showtip(self, event=None):
        x = y = 0
        x_left, y_top, x_right, y_bottom = self.widget.bbox("insert")
        x += self.widget.winfo_rootx() + x_right + 10
        y += self.widget.winfo_rooty() + y_bottom + 10
        # creates a toplevel window
        self.tw = ctk.CTkToplevel(self.widget)
        self.tw.overrideredirect(True)  # removes the window decorations
        self.tw.geometry(f"+{x}+{y}")
        self.tw.attributes("-topmost", True)  # Ensures tooltip is on top
        label = ctk.CTkLabel(self.tw, text=self.text, justify='left',
                             fg_color='lightyellow', corner_radius=4,
                             text_color='black', wraplength=self.wraplength)
        label.pack(ipadx=1)
    def hidetip(self):
        tw = self.tw
        self.tw= None
        if tw:
            tw.destroy()

class TowerApp:
    def __init__(self, root):
        super().__init__()
        self.root = root
        self.root.title("Warcraft 3 Tower Balancer by Aphotica (Discord: https://discord.gg/Qsg6UDn)")
        self.root.geometry("1455x910")  # Expanded width by 100 pixels
        self.root.resizable(False, True)
        self.validation_errors = False
        self.outlier_analysis_segments = []
        self.imported_df = pd.DataFrame()
        self.original_imported_df = pd.DataFrame()
        self.balance_ranges = {}
        self.global_dps_per_gold_ranges = {}
        self.global_raw_dps_ranges = {}
        self.outlier_analysis_segments = []
        self.changes_report = []
        self.typing_timer = None
        self.calculate_all_after_id = None # debounce mechanism using after_cancel and after to ensure calculate_all is not called excessively to prevent input lag
        self.importing_window = None
        

        # Register the validation function to allow only letters
        #self.validate_alpha = self.root.register(self.only_letters)

        # Set the appearance mode and color theme
        ctk.set_appearance_mode("dark")  # Options: "light", "dark", "system"
        ctk.set_default_color_theme("blue")  # Options: "blue", "green", "dark-blue"

        self.window_tracker = {
            'algorithm_editor': None,
            'dynamic_algorithm': None,
            'analysis': None,
            'help': None
        }

        self.focused_row = None

        self.towers = []
        self.balance_ranges = {}  # Will be dynamically calculated
        self.global_dps_per_gold_ranges = {}  # For storing global DPS/Gold ranges
        self.global_raw_dps_ranges = {}  # For storing global Raw DPS ranges

        # Target type balance adjustments
        self.target_type_balance_adjustments = {
            'All': (1.0, 1.0),  # (Low adjustment, High adjustment)
            'Ground Splash': (0.5, 1.5),
            'Air Splash': (0.5, 1.5),
        }

        # Preset balance ranges
        self.preset_balance_ranges = {
            1: (225, 325),
            2: (125, 175),
            3: (100, 125),
            4: (50, 75),
            5: (25, 30),
            6: (15, 25),
            7: (10, 15),
            8: (5, 10),
            9: (3, 5),
            10: (1, 3),
            11: (0.5, 1),
            12: (0.5, 1)
        }

        # Store the source code as a string
        self.source_code = ''

        # Initialize calculation function from code string
        self.calc_function_code = calculate_dps_per_gold_code
        exec_globals = {}
        exec(self.calc_function_code, exec_globals)
        self.calculate_dps_per_gold = exec_globals['calculate_dps_per_gold']

        # Desired canvas height to fit 11 towers without scrolling
        self.desired_canvas_height = None

        self.imported_df = pd.DataFrame()  # For storing imported data
        self.original_imported_df = pd.DataFrame()  # For storing original imported data

        self.setup_ui()

        # Bind keys 0-9 to call calculate_all
        for i in range(10):  # for keys 0 to 9
            self.root.bind(f"<Key-{i}>", self.on_key_press)
        self.root.bind('<Delete>', self.on_key_press)
        self.root.bind('<BackSpace>', self.on_key_press)
        self.root.bind('<Return>', self.on_enter_pressed) 

    def on_key_press(self, event):
        # Cancel any previously set timer if a new key is pressed
        if self.typing_timer:
            self.typing_timer.cancel()

        # Set a new timer to call calculate_all after a delay (e.g., 500ms)
        self.typing_timer = threading.Timer(1, self.run_calculate_all)
        self.typing_timer.start()

    def on_enter_pressed(self, event):
        """
        Checks if there are validation errors before running calculations.
        If validation errors exist, only acknowledges the error message without running calculations.
        """
        if self.validation_errors:
            self.show_validation_error_message()  # Show error message and skip calculation
            self.validation_errors = False  # Reset error flag after displaying message
        else:
            self.calculate_all()  # Run calculations if no errors

    def set_focused_row(self, row_frame):
        """
        Sets the given row_frame as the focused row and updates the background colors accordingly.
        Resets the background of the previously focused row if it's different from the current one.
        """
        if self.focused_row and self.focused_row != row_frame:
            try:
                if self.focused_row.winfo_exists():
                    self.focused_row.configure(fg_color="#1c1c1c")  # Reset previous row's background
            except tk.TclError:
                pass  # The focused row no longer exists

        self.focused_row = row_frame
        try:
            if self.focused_row.winfo_exists():
                self.focused_row.configure(fg_color="#7abdf5")  # Set current row's background to light blue
        except tk.TclError:
            self.focused_row = None  # Reset if the frame no longer exists

    def only_letters(self, proposed_text):
        """
        Validates that the proposed_text contains only alphabetic characters and allowed symbols.
        Allowed symbols can include space and hyphen.
        """
        allowed_symbols = " -"
        for char in proposed_text:
            if not (char.isalpha() or char in allowed_symbols):
                return False
        return True
    
    def setup_ui(self):
        self.main_frame = ctk.CTkFrame(self.root)
        self.main_frame.pack(fill=ctk.BOTH, expand=True)

        # Register the validation function
        vcmd = (self.root.register(self.only_letters), '%P')  # '%P' passes the proposed value of the entry

        # Configure grid layout for main_frame
        self.main_frame.grid_rowconfigure(1, weight=1)
        self.main_frame.grid_columnconfigure(0, weight=1)

        # Header Frame (Separate from towers)
        header_frame = ctk.CTkFrame(self.main_frame)
        header_frame.grid(row=0, column=0, sticky='ew', padx=10, pady=5)
        header_frame.grid_columnconfigure(0, weight=1)

        # Left side of header (Race Entry and Combobox)
        race_frame = ctk.CTkFrame(header_frame)
        race_frame.pack(side=ctk.LEFT, padx=(0, 20))

        race_label = ctk.CTkLabel(race_frame, text="Race:")
        race_label.grid(row=1, column=0, padx=(0,5), pady=2)

        self.race_entry = ctk.CTkEntry(race_frame, width=200, validate='key', validatecommand=vcmd)
        self.race_entry.grid(row=1, column=1, padx=(0,10), pady=2)

        # Race selection Combobox with increased width
        self.race_combobox = ctk.CTkComboBox(race_frame, values=[], state='readonly', command=self.on_race_selected, width=200)
        self.race_combobox.set('Select Race')  # Show 'Select Race' if no race is selected
        self.race_combobox.grid(row=0, column=1, padx=(0,10), pady=2)

        # Export and Import buttons in a frame
        export_import_frame = ctk.CTkFrame(header_frame)
        export_import_frame.pack(side=ctk.LEFT, padx=(0, 20))

        self.export_button = ctk.CTkButton(export_import_frame, text="Export", command=self.export_data)
        self.export_button.pack(side=ctk.LEFT, padx=5)

        self.import_button = ctk.CTkButton(export_import_frame, text="Import", command=self.import_data)
        self.import_button.pack(side=ctk.LEFT, padx=5)

        # Dynamic Comparison Checkbox
        self.dynamic_comparison_var = ctk.BooleanVar(value=True)
        self.dynamic_comparison_chk = ctk.CTkCheckBox(header_frame, text="Dynamic Comparison",
                                                    variable=self.dynamic_comparison_var, command=self.calculate_all)
        self.dynamic_comparison_chk.pack(side=ctk.LEFT, padx=5)

        # Ignore Outliers Checkbox
        self.ignore_outliers_var = ctk.BooleanVar(value=True)
        self.ignore_outliers_chk = ctk.CTkCheckBox(header_frame, text="Ignore Outliers",
                                                variable=self.ignore_outliers_var, command=self.calculate_all)
        self.ignore_outliers_chk.pack(side=ctk.LEFT, padx=5)

        # Options Button on the far right
        options_frame = ctk.CTkFrame(header_frame)
        options_frame.pack(side=ctk.RIGHT, padx=(0,10))

        self.options_button = ctk.CTkButton(options_frame, text="Options", command=self.open_options_window)
        self.options_button.pack(side=ctk.LEFT, padx=5)

        # Towers Frame Container (Separate from headers)
        towers_frame_container = ctk.CTkFrame(self.main_frame)
        towers_frame_container.grid(row=1, column=0, sticky='nsew', padx=10, pady=5)
        towers_frame_container.grid_rowconfigure(1, weight=1)
        towers_frame_container.grid_columnconfigure(0, weight=1)

        # Towers Header Frame (Separate headers from tower data)
        towers_header_frame = ctk.CTkFrame(towers_frame_container)
        towers_header_frame.grid(row=0, column=0, sticky='ew')
        # Call create_headers before configuring columns that depend on self.headers
        self.create_headers(towers_header_frame)
        towers_header_frame.grid_columnconfigure(len(self.headers)-1, weight=1)

        # Towers Frame with Scrollbar
        self.towers_canvas = ctk.CTkCanvas(towers_frame_container, bg='#1c1c1c', highlightthickness=0)
        self.towers_canvas.grid(row=1, column=0, sticky='nsew')

        towers_scrollbar = ctk.CTkScrollbar(towers_frame_container, orientation=ctk.VERTICAL, command=self.towers_canvas.yview)
        towers_scrollbar.grid(row=1, column=1, sticky='ns')

        self.towers_canvas.configure(yscrollcommand=towers_scrollbar.set)

        self.towers_frame = ctk.CTkFrame(self.towers_canvas, fg_color='#1c1c1c')
        self.towers_canvas.create_window((0, 0), window=self.towers_frame, anchor='nw')

        # Update scrollregion when towers_frame is resized
        self.towers_frame.bind("<Configure>", self.on_towers_frame_configure)

        # Bind scroll wheel only to the towers canvas
        self.towers_canvas.bind("<Enter>", lambda e: self.towers_canvas.bind_all("<MouseWheel>", self._on_mousewheel))
        self.towers_canvas.bind("<Leave>", lambda e: self.towers_canvas.unbind_all("<MouseWheel>"))

        # Create initial towers
        for _ in range(11):
            self.add_tower()

        # Buttons at the bottom
        bottom_button_frame = ctk.CTkFrame(self.main_frame)
        bottom_button_frame.grid(row=2, column=0, sticky='ew', padx=10, pady=5)
        bottom_button_frame.grid_columnconfigure(0, weight=1)

        self.calculate_button = ctk.CTkButton(bottom_button_frame, text="Calculate All", command=self.calculate_all)
        self.calculate_button.pack(side=ctk.LEFT, padx=5)

        # Clear All button
        self.clear_all_button = ctk.CTkButton(bottom_button_frame, text="Clear All", command=self.clear_all_towers)
        self.clear_all_button.pack(side=ctk.RIGHT, padx=5)

        self.delete_tower_button = ctk.CTkButton(bottom_button_frame, text="Delete Tower", command=self.delete_last_tower)
        self.delete_tower_button.pack(side=ctk.RIGHT, padx=5)
        
        self.add_tower_button = ctk.CTkButton(bottom_button_frame, text="Add Tower", command=self.add_tower)
        self.add_tower_button.pack(side=ctk.RIGHT, padx=5)

        # Result Text with Scrollbar (Adjusted height for 16 towers)
        result_frame = ctk.CTkFrame(self.main_frame)
        result_frame.grid(row=3, column=0, sticky='nsew', padx=10, pady=10)
        result_frame.grid_rowconfigure(0, weight=1)
        result_frame.grid_columnconfigure(0, weight=1)

        self.result_text = tk.Text(result_frame, height=16, wrap='none', bg='#2E2E2E', font=("Consolas", 11))  # Changed height from 20 to 16
        self.result_text.grid(row=0, column=0, sticky='nsew')

        result_scrollbar = ctk.CTkScrollbar(result_frame, orientation=ctk.VERTICAL, command=self.result_text.yview)
        self.result_text.configure(yscrollcommand=result_scrollbar.set)
        result_scrollbar.grid(row=0, column=1, sticky='ns')

        # Configure text widget tags for coloring
        self.result_text.tag_configure("green", foreground="#00D1A0")
        self.result_text.tag_configure("red", foreground="#FF4C4C")
        self.result_text.tag_configure("yellow", foreground="#FFFF00")  # Added for yellow color
        self.result_text.tag_configure("blue", foreground="#00CED1")  # For tower numbers
        self.result_text.tag_configure("header", foreground="blue", font=("Helvetica", 12, "bold"))
        self.result_text.tag_configure("outlier_header", foreground="#FFFF00", font=("Helvetica", 12, "bold"))

        # Make the result_text read-only
        self.result_text.configure(state=tk.DISABLED)

    def start_tab_monitoring(self, tabview):
        """
        Starts the periodic check to monitor tab changes for a given tabview.
        """
        self.last_selected_tab = tabview.get()
        self.current_monitored_tabview = tabview
        self.check_tab_change()

    def check_tab_change(self):
        """
        Checks if the selected tab has changed in the monitored tabview.
        If "View Changes" tab is selected, runs calculate_all.
        """
        if hasattr(self, 'current_monitored_tabview') and self.current_monitored_tabview.winfo_exists():
            current_tab = self.current_monitored_tabview.get()
            if current_tab != self.last_selected_tab:
                self.last_selected_tab = current_tab
                if current_tab == "View Changes":
                    self.calculate_all()
        # Schedule the next check after 1000 milliseconds
        self.root.after(1000, self.check_tab_change)

    def open_options_window(self):
        if self.window_tracker.get('options_window') is not None:
            try:
                self.window_tracker['options_window'].lift()
                self.window_tracker['options_window'].focus_force()
            except tk.TclError:
                self.window_tracker['options_window'] = None
        if self.window_tracker.get('options_window') is None:
            options_win = ctk.CTkToplevel(self.root)
            self.window_tracker['options_window'] = options_win
            options_win.title("Options")
            # Set options window size to match main window height
            main_height = self.root.winfo_height()
            options_win.geometry(f"800x{main_height}")
            options_win.resizable(True, True)

            # Position the options window to the right of the main window
            main_x = self.root.winfo_x()
            main_y = self.root.winfo_y()
            main_width = self.root.winfo_width()
            options_x = main_x + main_width + 10  # 10 pixels gap
            options_win.geometry(f"+{options_x}+{main_y}")

            # Bind the destroy event to reset the tracker when the window is closed
            options_win.protocol("WM_DELETE_WINDOW", lambda: self.close_window('options_window', options_win))
            options_win.bind("<Escape>", lambda event: self.close_window('options_window', options_win))

            # Create the tab view
            tabview = ctk.CTkTabview(options_win)
            tabview.pack(fill='both', expand=True)

            # Add tabs
            tabview.add("Analysis")
            tabview.add("Help")
            tabview.add("Algorithm")
            tabview.add("Dynamic Algorithm")
            tabview.add("View Changes")

            # Implement the content for each tab
            self.create_help_tab(tabview.tab("Help"))
            self.create_algorithm_tab(tabview.tab("Algorithm"))
            self.create_dynamic_algorithm_tab(tabview.tab("Dynamic Algorithm"))
            self.create_analysis_tab(tabview.tab("Analysis"))
            self.create_view_changes_tab(tabview.tab("View Changes"))

            # After creating the tabview
            self.start_tab_monitoring(tabview)


    def create_help_tab(self, parent):
        help_text_frame = ctk.CTkFrame(parent)
        help_text_frame.pack(fill=ctk.BOTH, expand=True, padx=10, pady=10)

        help_text = tk.Text(help_text_frame, wrap='word', bg='#1e1e1e', fg='#f5f5f5', font=("Arial", 11))
        help_text.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)

        help_scrollbar = ctk.CTkScrollbar(help_text_frame, orientation=ctk.VERTICAL, command=help_text.yview)
        help_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        help_text.configure(yscrollcommand=help_scrollbar.set)

        # Define help content
        help_content = """
    Warcraft 3 Tower Balancer Tool: User Guide

    Overview
    --------
    The Warcraft 3 Tower Balancer Tool is a comprehensive utility for balancing tower stats within custom Warcraft 3 maps. Designed by Aphotica, this tool provides an interactive interface to calculate various balance metrics such as DPS per Gold, Z-Score, and Percent Rank. Additionally, it offers functionalities to import/export data, perform outlier analysis, and customize algorithms.

    Features
    --------
    1. **Dynamic Comparison**: Automatically calculates and adjusts balance ranges based on imported data.
    2. **Outlier Detection**: Identifies towers that deviate significantly from standard values, making it easy to spot overpowered or underpowered units.
    3. **Algorithm Customization**: Adjust the calculation logic to fit unique balancing needs by modifying the algorithm directly in the tool.
    4. **Import/Export Capabilities**: Save and load tower configurations as needed for easier testing and balancing across multiple maps or scenarios.
    5. **Race Difficulty**: Assess race difficulty on a scale from 1-10 (10 being hardest to play) based on overall race DPS/Gold, Raw DPS, Range, Splash, and Abilities.

    Getting Started
    ---------------
    1. **Import Data**: 
    Use the **Import** button to load existing tower data. Supported formats include Excel files with necessary columns. Ensure your dataset includes essential columns such as **Race**, **Tower Number**, **Gold Cost**, **Damage**, etc.
    Columns MUST read in order: Name, Gold Cost, Damage, Dice, Sides, Cooldown, Range, Full Splash, Med Splash, Small Splash, Spell DPS, Spell DPS CD, Slow %, Utility Boost, Poison (0 or 1), Target Type, Z-Score, Percent Rank, Race, Tower Number

    ***If uncertain, just use the tool to create the excel for you and continue exporting to add to it.***

    2. **Edit or Add New Towers**:
    Choose an existing race from the dropdown or type a new race name. Add new towers or edit existing ones by filling in fields like **Name**, **Gold Cost**, **Damage**, **Dice**, **Cooldown**, and more. Use **Add Tower** or **Delete Tower** to adjust the tower list.

    3. **Run Calculations**:
    Click **Calculate All** to perform the analysis. View calculated DPS, DPS per Gold, and any outliers in the **Results** section.

    4. **Analyze Results**:
    Open the **Analysis** tab to examine outliers, balance ranges, and specific metrics. Use the **View Changes** tab to see differences in tower data post-editing.

    5. **Export Data**:
    Save your work using the **Export** button. This will store your tower configuration and analysis results for future reference or sharing.

    Calculations and Algorithm
    --------------------------
    **Core Calculation (DPS per Gold)**

    The tool calculates DPS per Gold based on the following formula:

    DPS = (Base Damage + Dice * Average Die Roll) * (1 / Cooldown)
    Adjusted by **Range Modifier** and **Splash Damage** values, including **Full Splash**, **Medium Splash**, and **Small Splash** percentages.

    Utility Adjustments:
    Factors in special effects such as **Poison** and **Slow** which influence DPS based on target exposure and movement. **Utility Boost** can scale DPS based on additional benefits.

    Output Metrics:
    - **Total DPS**: Total calculated damage per second, considering range, splash, poison, and other adjustments.
    - **DPS per Gold**: Calculated as (Total DPS / Gold Cost) * 100, providing a standard measure of efficiency relative to cost.

    Dynamic Algorithm (For Users with Fewer than 20 Races)
    ------------------------------------------------------
    If fewer than 20 races are present, use the **Dynamic Algorithm** tab to configure presets. This dynamically adjusts DPS ranges by calculating mean and standard deviations of existing towers.

    Troubleshooting Tips
    --------------------
    - **Error Messages**: If calculation errors appear, verify that all essential fields are filled correctly. Missing or non-numeric values in key fields (like **Gold Cost** or **Cooldown**) can result in calculation errors.

    - **Outliers**: If outliers are identified, consider adjusting tower parameters or using the **Dynamic Comparison** feature to auto-adjust balance ranges.

    - **Custom Algorithm Adjustments**: In the **Algorithm** tab, modify the DPS formula or range modifiers to suit different gameplay styles. Save changes to the algorithm to apply custom calculations universally across all towers.

    Contact
    ----------
    Contact Aphotica on the Wintermaul Wars Discord server for assistance.
        """

        # Insert help content and apply tags for dynamic sections
        help_text.insert(tk.END, help_content)

        # Dynamic tags
        sections = {
            "title": ("Warcraft 3 Tower Balancer Tool: User Guide", "#00d1a0", ("Arial", 18, "bold italic")),
            "section": [
                ("Overview", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Features", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Getting Started", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Calculations and Algorithm", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Dynamic Algorithm", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Troubleshooting Tips", "#00d1a0", ("Arial", 16, "bold italic")),
                ("Contact", "#00d1a0", ("Arial", 16, "bold italic"))
            ],
            "subsection": [
                ("Dynamic Comparison", "#FFBF00", ("Arial", 13, "bold")),
                ("Outlier Detection", "#FFBF00", ("Arial", 13, "bold")),
                ("Algorithm Customization", "#FFBF00", ("Arial", 13, "bold")),
                ("Import/Export Capabilities", "#FFBF00", ("Arial", 13, "bold")),
                ("Race Difficulty", "#FFBF00", ("Arial", 13, "bold")),
                ("Import Data", "#FFBF00", ("Arial", 13, "bold")),
                ("Edit or Add New Towers", "#FFBF00", ("Arial", 13, "bold")),
                ("Run Calculations", "#FFBF00", ("Arial", 13, "bold")),
                ("Analyze Results", "#FFBF00", ("Arial", 13, "bold")),
                ("Export Data", "#FFBF00", ("Arial", 13, "bold")),
                ("Core Calculation (DPS per Gold)", "#FFBF00", ("Arial", 13, "bold")),
                ("Output Metrics", "#FFBF00", ("Arial", 13, "bold")),
                ("Error Messages", "#FFBF00", ("Arial", 13, "bold")),
                ("Outliers", "#FFBF00", ("Arial", 13, "bold")),
                ("Custom Algorithm Adjustments", "#FFBF00", ("Arial", 13, "bold"))
            ]
        }

        # Apply tags based on keywords
        for tag, values in sections.items():
            if isinstance(values, tuple):
                keyword, color, font = values
                start_index = help_content.index(keyword)
                end_index = start_index + len(keyword)
                help_text.tag_add(tag, f"1.0+{start_index}c", f"1.0+{end_index}c")
                help_text.tag_config(tag, foreground=color, font=font)
            else:
                for keyword, color, font in values:
                    start_index = help_content.index(keyword)
                    end_index = start_index + len(keyword)
                    help_text.tag_add(tag, f"1.0+{start_index}c", f"1.0+{end_index}c")
                    help_text.tag_config(tag, foreground=color, font=font)

        # Disable editing
        help_text.configure(state=tk.DISABLED)






    def create_algorithm_tab(self, parent):
        parent.grid_rowconfigure(0, weight=1)
        parent.grid_columnconfigure(0, weight=1)

        calc_label = ctk.CTkLabel(master=parent, text="Calculation Function (Python Code):", anchor="w")
        calc_label.grid(row=0, column=0, sticky="nw", padx=10, pady=5)
        self.calc_function_text = ctk.CTkTextbox(master=parent, width=760, height=400)
        self.calc_function_text.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")

        # Load the calculation function code from self.calc_function_code
        self.calc_function_text.insert("0.0", self.calc_function_code)

        # Adjusted balance ranges to be displayed vertically
        ranges_label = ctk.CTkLabel(master=parent, text="Preset Balance Ranges (Customizable):", anchor="w")
        ranges_label.grid(row=2, column=0, sticky="nw", padx=10, pady=5)
        self.ranges_text = ctk.CTkTextbox(master=parent, width=760, height=200)
        self.ranges_text.grid(row=3, column=0, padx=10, pady=5, sticky="nsew")

        # Load current preset ranges
        ranges_code = '{\n' + ',\n'.join([f"    {key}: {value}" for key, value in sorted(self.preset_balance_ranges.items())]) + '\n}'
        self.ranges_text.insert("0.0", ranges_code)

        # Target Type Balance Adjustments
        adjustments_label = ctk.CTkLabel(master=parent, text="Target Type Balance Adjustments (Python Dict Format):", anchor="w")
        adjustments_label.grid(row=4, column=0, sticky="nw", padx=10, pady=5)
        self.target_type_adjustments_text = ctk.CTkTextbox(master=parent, width=760, height=100)
        self.target_type_adjustments_text.grid(row=5, column=0, padx=10, pady=5, sticky="nsew")

        # Load current target type adjustments
        adjustments_code = '{\n' + ',\n'.join([f"    '{key}': {value}" for key, value in self.target_type_balance_adjustments.items()]) + '\n}'
        self.target_type_adjustments_text.insert("0.0", adjustments_code)

        # Buttons
        button_frame = ctk.CTkFrame(master=parent)
        button_frame.grid(row=6, column=0, pady=10)

        save_button = ctk.CTkButton(master=button_frame, text="Save/Apply", command=self.apply_algorithm_changes)
        save_button.pack(side=ctk.LEFT, padx=5)

        save_file_button = ctk.CTkButton(master=button_frame, text="Save to File", command=self.save_algorithm_to_file)
        save_file_button.pack(side=ctk.LEFT, padx=5)

        load_button = ctk.CTkButton(master=button_frame, text="Load from File", command=self.load_algorithm)
        load_button.pack(side=ctk.LEFT, padx=5)

    def create_dynamic_algorithm_tab(self, parent):
        parent.grid_rowconfigure(0, weight=1)
        parent.grid_columnconfigure(0, weight=1)

        dynamic_calc_label = ctk.CTkLabel(master=parent, text="Dynamic Balance Range Calculation:", anchor="w")
        dynamic_calc_label.grid(row=0, column=0, sticky="nw", padx=10, pady=5)

        self.dynamic_calc_text = ctk.CTkTextbox(master=parent, width=760, height=650)
        self.dynamic_calc_text.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")

        # Load the dynamic calculation code
        dynamic_code = '''
    ### Dynamic Balance Range Calculation
    # Outlier Removal: Uses IQR to exclude extreme outliers.
    # Mean and Std Dev: Calculates mean and standard deviation for DPS per Gold.
    # Scaling Factor: Applies a scaling factor inversely proportional to the tower number.

    def calculate_dynamic_balance(df):
        balance_ranges = {}
        grouped = df.groupby(['Tower Number', 'Target Type'])
        for (tower_num, target_type), group in grouped:
            Q1 = group['DPS per Gold'].quantile(0.25)
            Q3 = group['DPS per Gold'].quantile(0.75)
            IQR = Q3 - Q1
            filtered = group[(group['DPS per Gold'] >= Q1 - 1.5 * IQR) & (group['DPS per Gold'] <= Q3 + 1.5 * IQR)]
            if filtered.empty:
                filtered = group
            mean = filtered['DPS per Gold'].mean()
            std = filtered['DPS per Gold'].std(ddof=0)
            if std == 0:
                std = mean * 0.1
            low = mean - std
            high = mean + std
            scaling_factor = 1 / (tower_num ** 0.05)
            low *= scaling_factor
            high *= scaling_factor
            balance_ranges[(tower_num, target_type)] = (low, high)
        return balance_ranges
        '''

        self.dynamic_calc_text.insert("end", dynamic_code)
        self.dynamic_calc_text.configure(state="disabled")  # Make the text read-only

        # Comments explaining each part
        comments_text = '''
    # Explanation of Key Components:
    # 1. Outlier Removal: This section uses IQR (Interquartile Range) to exclude extreme outliers from the DPS per Gold calculation.
    #    You can modify the IQR multiplier (currently 1.5) to adjust how strict the outlier removal process is.
    # 2. Mean and Standard Deviation: These are used to calculate the average DPS per Gold and its acceptable range.
    # 3. Scaling Factor: As tower numbers increase, this factor slightly widens the acceptable range of balance for more expensive or powerful towers.
    #    Adjusting the exponent (currently 0.05) will impact how much flexibility is allowed for higher-tier towers.
        '''
        comments_label = ctk.CTkLabel(master=parent, text=comments_text, justify='left', wraplength=760, anchor='nw')
        comments_label.grid(row=2, column=0, padx=10, pady=5, sticky="nsew")



    def create_view_changes_tab(self, parent):
        """
        Creates the "View Changes" tab within the Options window.
        Displays the list of changes made to towers.
        
        Parameters:
        - parent: The parent frame or tab where the View Changes tab will be placed.
        """
        # Set up the main frame for the View Changes tab
        view_changes_frame = ctk.CTkFrame(parent)
        view_changes_frame.pack(fill=ctk.BOTH, expand=True, padx=10, pady=10)
        
        # Use a Text widget for the changes, enabling color-coded tags
        changes_text = tk.Text(view_changes_frame, wrap='word', bg='#333333', fg='white', font=("Consolas", 11))
        changes_text.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)
        
        # Add a scrollbar
        changes_scrollbar = ctk.CTkScrollbar(view_changes_frame, orientation=ctk.VERTICAL, command=changes_text.yview)
        changes_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        changes_text.configure(yscrollcommand=changes_scrollbar.set)
        
        # Store the text widget for future updates
        self.view_changes_text = changes_text
        
        # Configure color tags
        changes_text.tag_configure("green", foreground="#00D1A0")
        changes_text.tag_configure("red", foreground="#FF4C4C")
        changes_text.tag_configure("yellow", foreground="#FFFF00")
        changes_text.tag_configure("blue", foreground="#00CED1")
        changes_text.tag_configure("header", foreground="#FFFF00", font=("Consolas", 12, "bold"))  # For "Outlier Analysis"
        changes_text.tag_configure("outlier_header", foreground="red", font=("Consolas", 12, "bold"))  # For "Low-End Outliers" and "High-End Outliers"
        changes_text.tag_configure("race_header", foreground="green", font=("Consolas", 12, "bold"))  # For Race name
        changes_text.tag_configure("difficulty_white", foreground="white", font=("Consolas", 12))
        changes_text.tag_configure("difficulty_green", foreground="green", font=("Consolas", 12))
        changes_text.tag_configure("difficulty_orange", foreground="orange", font=("Consolas", 12))
        changes_text.tag_configure("difficulty_red", foreground="red", font=("Consolas", 12))
        
        # Insert the changes report if available
        if hasattr(self, 'changes_report') and self.changes_report:
            for change_line in self.changes_report:
                for segment in change_line:
                    if len(segment) >= 2:
                        text, color = segment[:2]
                        bold = segment[2] if len(segment) > 2 else False
                        tag = color + ("_bold" if bold else "")
                        if tag not in changes_text.tag_names():
                            font_style = ("Consolas", 12, "bold") if bold else ("Consolas", 12)
                            changes_text.tag_configure(tag, foreground=color, font=font_style)
                        changes_text.insert("end", text, tag)
        else:
            # Display default message when there's no data
            changes_text.insert("end", "Import data or add races to view outlier analysis and race difficulty levels.\n", "white")
        
        # Disable editing
        changes_text.configure(state=tk.DISABLED)




    def update_view_changes_tab(self):
        """
        Updates the "View Changes" tab with the latest changes_report.
        """
        if hasattr(self, 'view_changes_text'):
            changes_text = self.view_changes_text
            changes_text.configure(state=tk.NORMAL)
            changes_text.delete("1.0", "end")  # Clear existing content

            # Define all necessary tags with their color configurations
            predefined_tags = {
                "green": {"foreground": "green", "font": ("Consolas", 12)},
                "red": {"foreground": "red", "font": ("Consolas", 12)},
                "orange": {"foreground": "orange", "font": ("Consolas", 12)},
                "blue": {"foreground": "#4DA6FF", "font": ("Consolas", 12, "bold")},
                "yellow": {"foreground": "#FFFF00", "font": ("Consolas", 12, "bold")},
                "light_yellow": {"foreground": "#FFD966", "font": ("Consolas", 12, "bold")},
                "dark_turquoise": {"foreground": "#4DA6FF", "font": ("Consolas", 12, "bold")},
                "light_gray": {"foreground": "#A0A0A0", "font": ("Consolas", 12)},
                "white": {"foreground": "white", "font": ("Consolas", 12)},
                "air_target": {"foreground": "#00CED1", "font": ("Consolas", 12)},
                "balanced": {"foreground": "green", "font": ("Consolas", 12)},
                "overpowered": {"foreground": "red", "font": ("Consolas", 12)},
                "underpowered": {"foreground": "red", "font": ("Consolas", 12)},
                # Add more tags as needed
            }

            # Configure all predefined tags
            for tag_name, tag_attrs in predefined_tags.items():
                if tag_name not in changes_text.tag_names():
                    changes_text.tag_configure(tag_name, **tag_attrs)

            # Insert the changes report if available
            if hasattr(self, 'changes_report') and isinstance(self.changes_report, list) and self.changes_report:
                for change_line in self.changes_report:
                    for segment in change_line:
                        if len(segment) >= 2:
                            text, color = segment[:2]
                            bold = segment[2] if len(segment) > 2 else False
                            # Map the color to a predefined tag or use default
                            if color in predefined_tags:
                                tag = color + ("_bold" if bold else "")
                            else:
                                tag = "white"  # Default tag
                            if tag not in changes_text.tag_names():
                                # Define a default tag if not predefined
                                font_style = ("Consolas", 12, "bold") if bold else ("Consolas", 12)
                                changes_text.tag_configure(tag, foreground=color if color in ['green', 'red', 'orange', 'blue', 'yellow', 'light_yellow', 'dark_turquoise', 'light_gray', 'white', 'air_target', 'balanced', 'overpowered', 'underpowered'] else "white", font=font_style)
                            changes_text.insert("end", text, tag)
            else:
                # Display default message when there's no data
                changes_text.insert("end", "Import data or add races to view outlier analysis and race difficulty levels.\n", "white")

            # Disable editing
            changes_text.configure(state=tk.DISABLED)




    def generate_changes_report(self):
        """
        Generates a report of changes between the original and current data.
        Returns a list of lists, where each inner list represents a line composed of segments.
        Each segment is a tuple: (text, color, bold).
        """
        report_lines = []
        if self.original_imported_df.empty:
            report_lines.append([("No original data to compare changes.", "white", False)])
            return report_lines

        # Save current race data before generating report
        self.save_current_race_data()

        races = sorted(self.imported_df['Race'].unique())

        for race in races:
            original_race_df = self.original_imported_df[self.original_imported_df['Race'] == race]
            current_race_df = self.imported_df[self.imported_df['Race'] == race]

            # Merge on Tower Number to compare towers
            merged_df = pd.merge(original_race_df, current_race_df, on='Tower Number', suffixes=('_orig', '_curr'))

            changes_found = False
            race_title = race + ":\n"
            report_lines.append([(race_title, "green", True)])  # Race name in green, bold

            for _, row in merged_df.iterrows():
                tower_changes = []
                for col in ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                            'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                            'Slow %', 'Utility Boost', 'Poison', 'Target Type']:
                    orig_value = row.get(f"{col}_orig", '')
                    curr_value = row.get(f"{col}_curr", '')
                    if pd.isnull(orig_value):
                        orig_value = '0'
                    if pd.isnull(curr_value):
                        curr_value = '0'

                    # Ignore specific fields as per your requirements
                    if col == 'Spell DPS' and (float(orig_value or 0.0) == 0.0 and float(curr_value or 0.0) == 0.0):
                        continue
                    if col == 'Utility Boost' and (float(orig_value or 1.0) == 1.0 and float(curr_value or 1.0) == 1.0):
                        continue
                    if col in ['Slow %', 'Spell DPS CD']:
                        orig_value_float = float(orig_value or 0.0)
                        curr_value_float = float(curr_value or 0.0)
                        if (orig_value_float in [0.0, 0, 1.0, 1]) and (curr_value_float in [0.0, 0, 1.0, 1]):
                            continue

                    # Compare values numerically to handle trailing zeroes
                    change_detected = False
                    try:
                        orig_num = float(orig_value)
                        curr_num = float(curr_value)
                        if orig_num == curr_num:
                            change_detected = False
                        else:
                            change_detected = True
                    except ValueError:
                        # For non-numeric values, compare as strings
                        if str(orig_value).strip() == str(curr_value).strip():
                            change_detected = False
                        else:
                            change_detected = True

                    if change_detected:
                        # Determine if the value increased or decreased
                        if isinstance(orig_num, float) and isinstance(curr_num, float):
                            if curr_num > orig_num:
                                # Value increased
                                from_color = "red"
                                to_color = "green"
                            else:
                                # Value decreased
                                from_color = "green"
                                to_color = "red"
                        else:
                            # For non-numeric changes, default colors
                            from_color = "red"
                            to_color = "green"

                        change_segments = [
                            ("    - ", "white", False),  # Indent and bullet
                            (row['Name_curr'] + ": ", "#FFC107", True),  # Tower name in amber color, bold
                            (col, "#FFC107", True),  # Variable name in amber color, bold
                            (" changed from ", "white", False),
                            (str(orig_value), from_color, False),  # Original value
                            (" to ", "white", False),
                            (str(curr_value), to_color, False),  # New value
                            ("\n", "white", False)
                        ]
                        tower_changes.append(change_segments)
                        changes_found = True

                if tower_changes:
                    # Add changes for this tower
                    for change in tower_changes:
                        report_lines.append(change)
                    # Add a blank line after each tower
                    report_lines.append([("\n", "white", False)])

            if not changes_found:
                # If no changes for this race, remove the race header
                report_lines.pop()
            else:
                # Add only one blank line between races
                report_lines.append([("\n", "white", False)])

        if not report_lines:
            report_lines.append([("No changes detected across the data set.", "white", False)])

        self.changes_report = report_lines  # Store the changes report

        return report_lines








    def toggle_ignore_outliers(self):
        if self.dynamic_comparison_var.get():
            self.ignore_outliers_chk.pack(side=ctk.LEFT, padx=5)  # Show if Dynamic Comparison is checked
        else:
            self.ignore_outliers_chk.pack_forget()  # Hide otherwise

    def show_clear_all_confirmation(self):
        # Create a new Toplevel window for the custom confirmation dialog
        confirmation_dialog = tk.Toplevel(self.root)
        confirmation_dialog.title("Confirm Clear All")
        confirmation_dialog.geometry("350x150")
        confirmation_dialog.configure(bg="#151924")  # Set background color of Toplevel window

        # Center the dialog on the main window
        self.center_window(confirmation_dialog, 350, 150)

        # Ensure it stays on top and restricts interaction with the main window
        confirmation_dialog.transient(self.root)
        confirmation_dialog.grab_set()

        # Add a bold red warning label
        warning_label = ctk.CTkLabel(
            confirmation_dialog,
            text="WARNING: Unsaved data will be lost",
            text_color="#FF3333",
            font=("Arial", 16, "bold"),
            fg_color="#151924",  # Set the background for customtkinter label
            anchor="center"
        )
        warning_label.pack(pady=(20, 10))

        # Add the confirmation question
        question_label = ctk.CTkLabel(
            confirmation_dialog,
            text="Are you sure you want to clear all data?",
            fg_color="#151924",  # Set the background for customtkinter label
            anchor="center"
        )
        question_label.pack(pady=5)

        # Frame for the Yes and No buttons
        button_frame = ctk.CTkFrame(confirmation_dialog, fg_color="#151924")
        button_frame.pack(pady=15)

        # "Yes" button to confirm
        yes_button = ctk.CTkButton(button_frame, text="Yes", command=lambda: self.confirm_clear_all(confirmation_dialog))
        yes_button.pack(side=ctk.LEFT, padx=10)

        # "No" button to cancel
        no_button = ctk.CTkButton(button_frame, text="No", command=confirmation_dialog.destroy)
        no_button.pack(side=ctk.LEFT, padx=10)

    # Center a Window (used for "Clear All")
    def center_window(self, window, width, height):
        """Center a window on the screen or main application window."""
        x = self.root.winfo_x() + (self.root.winfo_width() // 2) - (width // 2)
        y = self.root.winfo_y() + (self.root.winfo_height() // 2) - (height // 2)
        window.geometry(f"{width}x{height}+{x}+{y}")
    
    # Center a window with timer (prompts where acknowledgement is not necessary for function to run)
    def show_centered_message(self, message, duration=2000):
        message_win = tk.Toplevel(self.root)
        message_win.overrideredirect(True)
        message_win.geometry(f"400x100+{self.root.winfo_x() + (self.root.winfo_width() // 2) - 150}+{self.root.winfo_y() + (self.root.winfo_height() // 2) - 50}")
        message_win.configure(bg="#151924")

        label = ctk.CTkLabel(message_win, text=message, text_color="white", font=("Arial", 14))
        label.pack(expand=True, fill='both')

        # Destroy the message window after the duration
        message_win.after(duration, message_win.destroy)


    def show_importing_message(self, message="Loading races..."):
        """
        Displays a centered importing message window with a dynamic label.
        
        Parameters:
        - message (str): The initial message to display.
        """
        if self.importing_window and tk.Toplevel.winfo_exists(self.importing_window):
            # Importing window already exists
            return

        self.importing_window = tk.Toplevel(self.root)
        self.importing_window.title("Importing Data")
        self.importing_window.geometry("450x120")
        self.importing_window.resizable(False, False)
        self.importing_window.configure(bg="#333333")  # Dark background

        # Make the window modal and disable the close button
        self.importing_window.transient(self.root)
        self.importing_window.grab_set()
        self.importing_window.protocol("WM_DELETE_WINDOW", lambda: None)  # Disable close button

        # Center the window
        self.center_window(self.importing_window, 450, 120)

        # Initial message label
        self.importing_message_label = tk.Label(
            master=self.importing_window,
            text=message,
            fg="white",
            bg="#333333",
            font=("Arial", 14, "bold")
        )
        self.importing_message_label.pack(expand=True, fill='both', padx=20, pady=20)

        # Force the window to render
        self.importing_window.update()




    def hide_importing_message(self):
        """
        Hides the importing message window if it exists.
        """
        if hasattr(self, 'importing_window') and self.importing_window is not None:
            try:
                self.importing_window.destroy()
            except tk.TclError:
                pass  # The window might have already been destroyed
            self.importing_window = None

    def confirm_clear_all(self, dialog):
        dialog.destroy()  # Close the confirmation dialog
        
        # Proceed with clearing all towers and race fields
        for tower in self.towers:
            self.clear_tower_fields(tower)  # Assuming clear_tower_fields is defined to reset fields

        # Clear the race name field
        self.race_entry.configure(state='normal')
        self.race_entry.delete(0, ctk.END)
        self.race_entry.configure(state='normal')
        
        # Reset the dropdown to "Select Race"
        self.race_combobox.set("Select Race")

    def show_calculation_error(self, error_message):
        # Create a custom Toplevel window
        error_dialog = tk.Toplevel(self.root)
        error_dialog.title("Calculation Error")
        error_dialog.geometry("300x150")
        error_dialog.configure(bg="#1c1c1c")  # Dark background color

        # Center the dialog on the main window
        self.center_window(error_dialog, 300, 150)

        # Prevent interaction with the main window until closed
        error_dialog.transient(self.root)
        error_dialog.grab_set()

        # Add an error message label
        error_label = ctk.CTkLabel(
            error_dialog,
            text="Calculation Error",
            text_color="#FF3333",  # Red color for the title to highlight the error
            font=("Arial", 14, "bold"),
            fg_color="#1c1c1c",  # Dark background color for label
            anchor="center"
        )
        error_label.pack(pady=(10, 5))

        # Add the specific error message text
        message_label = ctk.CTkLabel(
            error_dialog,
            text=error_message,
            text_color="white",  # White color for the error details
            fg_color="#1c1c1c",  # Dark background color for label
            wraplength=280,
            anchor="center"
        )
        message_label.pack(pady=(5, 10))

        # Add a Close button to dismiss the dialog
        close_button = ctk.CTkButton(
            error_dialog,
            text="Close",
            command=error_dialog.destroy,
            fg_color="#333333",  # Button color matching the theme
            text_color="white"
        )
        close_button.pack(pady=10)


    # Update the clear_all_towers method to use the custom confirmation dialog
    def clear_all_towers(self):
        self.show_clear_all_confirmation()

    def on_entry_focus_in(self, col):
        """
        Changes the corresponding header label color to green when an entry gains focus.
        
        Parameters:
        - col (int): The column index of the focused entry.
        """
        if 0 <= col < len(self.header_labels):
            self.header_labels[col].configure(text_color="#FFC107")

    def on_entry_focus_out(self, col):
        """
        Resets the corresponding header label color to white when an entry loses focus.
        
        Parameters:
        - col (int): The column index of the unfocused entry.
        """
        if 0 <= col < len(self.header_labels):
            self.header_labels[col].configure(text_color="white")


    def create_headers(self, parent_frame):
        self.headers = ['No.', 'Name', 'Gold Cost', 'Damage', 'Dice','Sides\nper Die', 'Cooldown', 'Range', 'Full\nSplash', 'Med\nSplash', 'Small\nSplash', 'Spell\nDPS', 'Spell\nDPS CD', 'Slow %', 'Utility\nBoost', 'Poison', 'Target\nType']  # Updated 'Sides' to 'Sides per Die'

        tooltips = {
            'No.': 'Tower number',
            'Gold Cost': 'Cost of the tower in gold',
            'Damage': 'Base damage of the tower',
            'Dice': 'Number of dice rolled for damage',
            'Sides\nper Die': 'Number of sides on each die',  # Updated tooltip
            'Cooldown': 'Time between attacks (seconds)',
            'Range': 'Attack range of the tower',
            'Full\nSplash': 'Percentage chance of full splash damage',
            'Med\nSplash': 'Percentage chance of medium splash damage',
            'Small\nSplash': 'Percentage chance of small splash damage',
            'Spell\nDPS': 'Custom spell damage per second',
            'Spell\nDPS CD': 'Cooldown for spell DPS',
            'Slow %': 'Percentage reduction in movement speed',
            'Utility\nBoost': 'Damage multiplier for utility effects',
            'Poison': 'Applies poison effect that slows and damages over time',
            'Target\nType': 'Determines if a tower has specific splash damage criteria (All, Ground Splash, Air Splash)',
        }

        # Increased column widths for better readability and alignment
        self.column_widths = [30, 145, 85, 75, 60, 70, 80, 80, 80, 80, 75, 85, 75, 85, 85, 50, 115]  # width of the headers above tower data

        # Configure columns in parent_frame
        for idx in range(len(self.headers)):
            parent_frame.grid_columnconfigure(idx, weight=1)

        # Initialize a list to store header label widgets
        self.header_labels = []

        # Create headers with uniform background and increased width
        for idx, header in enumerate(self.headers):
            lbl = ctk.CTkLabel(parent_frame, text=header, anchor='w', width=self.column_widths[idx],
                            fg_color='transparent')  # Ensures uniform background
            lbl.grid(row=0, column=idx, padx=5, pady=2, sticky='nsew')
            lbl.configure(font=('Arial', 12, 'bold'))
            Tooltip(lbl, text=tooltips.get(header, ''))
            self.header_labels.append(lbl)  # Store the label in the list


    def on_towers_frame_configure(self, event):
        self.towers_canvas.configure(scrollregion=self.towers_canvas.bbox("all"))
        required_height = self.towers_frame.winfo_reqheight()
        if self.desired_canvas_height:
            if required_height <= self.desired_canvas_height:
                self.towers_canvas.configure(height=required_height)
                self.towers_canvas.yview_moveto(0)  # Reset the scroll position
            else:
                self.towers_canvas.configure(height=self.desired_canvas_height)
        else:
            self.towers_canvas.configure(height=required_height)

    def _on_mousewheel(self, event):
        # Scroll the towers_canvas when mouse wheel is used over the towers section
        self.towers_canvas.yview_scroll(int(-1*(event.delta/120)), "units")

    def close_window(self, window_type, window_instance):
        """
        Closes the given window and resets the window tracker for the specific window type.
        """
        # Destroy the window
        window_instance.destroy()

        # Reset the window tracker entry
        self.window_tracker[window_type] = None

    def create_analysis_tab(self, parent):
        # Set up the main frame for the Analysis tab
        analysis_text_frame = ctk.CTkFrame(parent)
        analysis_text_frame.pack(fill=ctk.BOTH, expand=True, padx=10, pady=10)

        # Use a Text widget for the analysis, enabling color-coded tags
        analysis_text = tk.Text(analysis_text_frame, wrap='word', bg='#333333', fg='white', font=("Consolas", 11))
        analysis_text.pack(side=ctk.LEFT, fill=ctk.BOTH, expand=True)

        # Add a scrollbar
        analysis_scrollbar = ctk.CTkScrollbar(analysis_text_frame, orientation=ctk.VERTICAL, command=analysis_text.yview)
        analysis_scrollbar.pack(side=ctk.RIGHT, fill=ctk.Y)
        analysis_text.configure(yscrollcommand=analysis_scrollbar.set)

        # Store the text widget for future updates
        self.analysis_text = analysis_text

        # Configure color tags like in calculate_all
        analysis_text.tag_configure("green", foreground="#00D1A0")
        analysis_text.tag_configure("red", foreground="#FF4C4C")
        analysis_text.tag_configure("yellow", foreground="#FFFF00")
        analysis_text.tag_configure("blue", foreground="#00CED1")
        analysis_text.tag_configure("header", foreground="blue", font=("Helvetica", 12, "bold"))
        analysis_text.tag_configure("outlier_header", foreground="#FFFF00", font=("Helvetica", 12, "bold"))

        # Display outlier analysis with color-coding
        if hasattr(self, 'outlier_analysis_segments'):
            for item in self.outlier_analysis_segments:
                if isinstance(item, tuple) and len(item) == 2:
                    text, color = item
                    tag = "red" if "Outliers" in text else color  # Use the red tag for headers
                    analysis_text.insert("end", text + "", tag)
                elif isinstance(item, tuple) and len(item) == 3:
                    text, color, bold = item
                    tag = color + ("_bold" if bold else "")
                    if tag not in analysis_text.tag_names():
                        font_style = ("Consolas", 12, "bold") if bold else ("Consolas", 12)
                        analysis_text.tag_configure(tag, foreground=color, font=font_style)
                    analysis_text.insert("end", text + "", tag)
                elif isinstance(item, list):
                    for text_segment, color_segment, *bold in item:
                        tag = color_segment + ("_bold" if bold else "")
                        if tag not in analysis_text.tag_names():
                            font_style = ("Consolas", 12, "bold") if bold else ("Consolas", 12)
                            analysis_text.tag_configure(tag, foreground=color_segment, font=font_style)
                        analysis_text.insert("end", text_segment + "", tag)
        analysis_text.configure(state=tk.DISABLED)

    def add_tower(self):
        row = len(self.towers)  # No need to offset by 1
        tower_fields = {}

        # Define specific widths for tower fields (separate from header widths)
        tower_column_widths = [30, 130, 80, 70, 50, 70, 70, 70, 70, 70, 70, 80, 70, 80, 80, 50, 80]

        # Create the original values dictionary for storing initial field values
        tower_fields['original_values'] = {
            'Gold Cost': '',
            'Damage': '',
            'Dice': '',
            'Sides': '',
            'Cooldown': '',
            'Range': '',
            'Full Splash': '',
            'Med Splash': '',
            'Small Splash': '',
            'Spell DPS': '',
            'Spell DPS CD': '',
            'Slow %': '',
            'Utility Boost': '',
            'Poison': 0,
            'Target Type': 'All'
        }

        # Create a Frame for the row
        row_frame = ctk.CTkFrame(self.towers_frame, fg_color='#1c1c1c')
        row_frame.grid(row=row, column=0, columnspan=len(self.headers), sticky='nsew', padx=0, pady=3)
        tower_fields['row_frame'] = row_frame

        # Configure columns in row_frame
        for idx in range(len(self.headers)):
            row_frame.grid_columnconfigure(idx, weight=1)

        # Bind events to highlight the row
        def on_enter_row(event, frame=row_frame):
            if frame != self.focused_row:
                frame.configure(fg_color='#6897bb')  # Light blue highlight

        def on_leave_row(event, frame=row_frame):
            if frame != self.focused_row:
                frame.configure(fg_color='#1c1c1c')  # Remove highlight

        def on_focus_row(event, frame=row_frame):
            self.set_focused_row(frame)  # Set this row as focused

        def on_focus_out_row(event, frame=row_frame):
            # Check if any widget in the row still has focus
            has_focus = any(widget.focus_displayof() for widget in frame.winfo_children())
            if not has_focus and self.focused_row == frame:
                frame.configure(fg_color='#1c1c1c')  # Reset background
                self.focused_row = None  # Unset the focused row

        # Tower number label
        tower_number_label = ctk.CTkLabel(row_frame, text=str(row+1), anchor='center', width=tower_column_widths[0], height=30, text_color="#ffffff")
        tower_number_label.grid(row=0, column=0, padx=2, pady=2, sticky='nsew')
        tower_fields['No.'] = tower_number_label

        # Create entries for each field
        fields = ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                'Slow %', 'Utility Boost']

        for col, field in enumerate(fields, start=1):
            entry = ctk.CTkEntry(row_frame, width=tower_column_widths[col], justify='center', text_color="white")
            entry.grid(row=0, column=col, padx=5, pady=2, sticky='nsew')
            tower_fields[field] = entry

            # Store the initial value in 'original_values'
            tower_fields['original_values'][field] = entry.get()

            # Bind mousewheel to each widget to ensure scrolling works when mouse is over them
            entry.bind("<MouseWheel>", self._on_mousewheel)
            
            # Bind events for highlighting and header color change
            entry.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
            entry.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
            entry.bind("<FocusIn>", lambda e, frame=row_frame, col=col: (on_focus_row(e, frame), self.on_entry_focus_in(col)))
            entry.bind("<FocusOut>", lambda e, frame=row_frame, col=col: (on_focus_out_row(e, frame), self.on_entry_focus_out(col)))


            # Bind event listeners for change detection with validation
            #entry.bind("<KeyRelease>", lambda e, field=field, tower_index=row: self.check_for_changes(tower_index, field))
            # Bind arrow key navigation
            entry.bind("<Up>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'up'))
            entry.bind("<Down>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'down'))
            entry.bind("<Left>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'left', e))
            entry.bind("<Right>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'right', e))

            # Add tooltip for each field
            tooltips = {
                'Name': 'Name of the tower',
                'Gold Cost': 'Cost of the tower in gold',
                'Damage': 'Base damage of the tower',
                'Dice': 'Number of dice rolled for damage',
                'Sides': 'Number of sides on each die',
                'Cooldown': 'Time between attacks (seconds)',
                'Range': 'Attack range of the tower',
                'Full Splash': 'Percentage chance of full splash damage',
                'Med Splash': 'Percentage chance of medium splash damage',
                'Small Splash': 'Percentage chance of small splash damage',
                'Spell DPS': 'Custom spell damage per second',
                'Spell DPS CD': 'Cooldown for spell DPS',
                'Slow %': 'Percentage reduction in movement speed',
                'Utility Boost': 'Damage multiplier for utility effects',
            }
            Tooltip(entry, text=tooltips.get(field, ''))

        # Poison Checkbutton
        poison_var = ctk.IntVar()
        poison_chk = ctk.CTkCheckBox(row_frame, text="", variable=poison_var, bg_color='#333333', command=self.calculate_all, width=20)
        poison_chk.grid(row=0, column=len(fields)+1, padx=2, pady=2, sticky='nsew')
        tower_fields['Poison'] = poison_var
        tower_fields['Poison_chk'] = poison_chk
        tower_fields['original_values']['Poison'] = poison_var.get()

        Tooltip(poison_chk, text='Applies poison effect that slows and damages over time')

        # Bind mousewheel to checkbutton
        poison_chk.bind("<MouseWheel>", self._on_mousewheel)
        # Bind events for highlighting
        poison_chk.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
        poison_chk.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
        poison_chk.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
        poison_chk.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

        # Bind event listener for the Poison checkbox change detection
        #changes(tower_index, field))

        # Target Type Combobox with decreased width
        target_type_var = ctk.StringVar()
        target_type_combobox = ctk.CTkComboBox(row_frame, variable=target_type_var, values=('All', 'Ground Splash', 'Air Splash'), state='readonly', width=80)
        target_type_combobox.set('All')  # default to 'All'
        target_type_combobox.grid(row=0, column=len(fields)+2, padx=2, pady=2, sticky='nsew')
        tower_fields['Target Type'] = target_type_var
        tower_fields['Target Type Combobox'] = target_type_combobox

        # Bind mousewheel to combobox
        target_type_combobox.bind("<MouseWheel>", self._on_mousewheel)
        # Bind events for highlighting
        target_type_combobox.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
        target_type_combobox.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
        target_type_combobox.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
        target_type_combobox.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

        # Add reset button
        reset_button = ctk.CTkButton(row_frame, text="Reset", width=60, command=lambda idx=len(self.towers): self.reset_tower(idx))
        reset_button.grid(row=0, column=len(fields)+3, padx=2, pady=2, sticky='nsew')
        tower_fields['reset_button'] = reset_button
        # Bind mousewheel to reset button
        reset_button.bind("<MouseWheel>", self._on_mousewheel)
        # Bind events for highlighting
        reset_button.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
        reset_button.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
        reset_button.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
        reset_button.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

        # Add tooltip for reset button
        Tooltip(reset_button, text='Reset this tower to default values')

        # Store the tower fields in the list of towers
        self.towers.append(tower_fields)



    def delete_tower(self, index):
        # Remove tower fields from the grid
        tower = self.towers[index]
        tower['row_frame'].destroy()
        # Remove the tower from the list
        self.towers.pop(index)
        # Reorder the remaining towers
        for idx in range(index, len(self.towers)):
            self.update_tower_row(self.towers[idx], idx)

    def delete_last_tower(self):
        if self.towers:
            self.delete_tower(len(self.towers) - 1)

    def update_tower_row(self, tower_fields, row):
        # Update the tower number label
        tower_number_label = tower_fields['No.']
        tower_number_label.configure(text=str(row+1))
        # Re-grid the row_frame
        tower_fields['row_frame'].grid(row=row, column=0, columnspan=len(self.headers), sticky='nsew')
        # Update reset button command
        reset_button = tower_fields['reset_button']
        reset_button.configure(command=lambda idx=row: self.reset_tower(idx))

    def reset_tower(self, index):
        if not self.original_imported_df.empty:
            # Get the race and tower number
            race_name = self.race_entry.get().strip()
            tower_number = index + 1
            # Ensure 'Tower Number' is integer
            self.original_imported_df['Tower Number'] = self.original_imported_df['Tower Number'].astype(int)
            # Strip whitespaces from 'Race' column
            self.original_imported_df['Race'] = self.original_imported_df['Race'].str.strip()
            # Filter for the specific tower from the original data
            tower_data = self.original_imported_df[(self.original_imported_df['Race'] == race_name) & (self.original_imported_df['Tower Number'] == tower_number)]
            if not tower_data.empty:
                # Populate the tower fields with original data
                self.populate_tower_fields(self.towers[index], tower_data.iloc[0])
                # Also update the temporary imported_df with the original data for this tower
                self.imported_df = self.imported_df[~((self.imported_df['Race'] == race_name) & (self.imported_df['Tower Number'] == tower_number))]
                self.imported_df = pd.concat([self.imported_df, tower_data], ignore_index=True)
            else:
                # Clear the fields if no original data is available
                self.clear_tower_fields(self.towers[index])
        else:
            # Clear the fields if no data is imported
            self.clear_tower_fields(self.towers[index])
        self.calculate_all()



    def populate_tower_fields(self, tower_fields, tower_row):
        # Clear fields before populating
        self.clear_tower_fields(tower_fields)

        # Define default values for specific fields
        default_values = {
            'Utility Boost': 1.0,
            'Slow %': 0,
            'Spell DPS': 0,
            'Spell DPS CD': 1,
            'Poison': 0,
            'Target Type': 'All'
        }

        # Populate fields
        integer_fields = ['Damage', 'Full Splash', 'Med Splash', 'Small Splash']
        for field in ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                    'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                    'Slow %', 'Utility Boost']:
            value = tower_row.get(field, '')
            if pd.isna(value) or value == 0 or value == 0.0:
                value = ''
            elif field in integer_fields:
                value = str(int(round(value)))
            elif field in default_values and float(value) == default_values[field]:
                # Leave the field blank if it has the default value
                value = ''
            else:
                value = str(value)

            # Insert the value into the entry widget
            tower_fields[field].insert(0, value)
            # Ensure text color is white
            tower_fields[field].configure(text_color="#FFFFFF" if value else "#FFFFFF")

        # Set checkboxes and comboboxes
        poison_value = tower_row.get('Poison', 0)
        tower_fields['Poison'].set(int(poison_value))
        target_type_value = tower_row.get('Target Type', 'All')
        tower_fields['Target Type'].set(target_type_value)

        for field, default in default_values.items():
            entry_widget = tower_fields.get(field)
            if entry_widget and hasattr(entry_widget, 'configure'):
                if field in integer_fields or field in default_values:
                    try:
                        current_value = float(tower_row.get(field, default))
                    except ValueError:
                        current_value = default
                    if current_value == default:
                        entry_widget.configure(text_color="#FFFFFF")  # Grey color for default
                    else:
                        entry_widget.configure(text_color="#FFFFFF")  # White color for user-set values

        # Update 'original_values' to reflect the current state
        for field in ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                    'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                    'Slow %', 'Utility Boost', 'Poison', 'Target Type']:
            if field in ['Poison', 'Target Type']:
                tower_fields['original_values'][field] = tower_fields[field].get()
            else:
                val = tower_fields[field].get()
                tower_fields['original_values'][field] = val if val else '0'


    def clear_tower_fields(self, tower_fields):
        fields_to_clear = [
            'Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
            'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
            'Slow %', 'Utility Boost'
        ]
        for field in fields_to_clear:
            entry_widget = tower_fields.get(field)
            if entry_widget:
                entry_widget.delete(0, ctk.END)

        # Uncheck the Poison checkbox
        poison_var = tower_fields.get('Poison')
        if poison_var:
            poison_var.set(0)

        # Reset Target Type to default ('All')
        target_type_var = tower_fields.get('Target Type')
        if target_type_var:
            target_type_var.set('All')

        # Clear Z-Score and Percent Rank
        # Assuming these are stored as attributes, adjust if stored differently
        # Since Z-Score and Percent Rank are not part of the GUI fields, this step might be unnecessary


    def navigate_entry(self, current_row, current_col, direction, event=None):
        if direction == 'up':
            if current_row > 0:
                target_entry = self.towers[current_row - 1][self.get_field_by_col(current_col)]
                target_entry.focus_set()
        elif direction == 'down':
            if current_row < len(self.towers) - 1:
                target_entry = self.towers[current_row + 1][self.get_field_by_col(current_col)]
                target_entry.focus_set()
        elif direction == 'left':
            entry = self.towers[current_row][self.get_field_by_col(current_col)]
            if event and entry.index(ctk.INSERT) == 0:
                if current_col > 0:
                    target_entry = self.towers[current_row][self.get_field_by_col(current_col - 1)]
                    target_entry.focus_set()
                    target_entry.icursor(ctk.END)
        elif direction == 'right':
            entry = self.towers[current_row][self.get_field_by_col(current_col)]
            if event and entry.index(ctk.INSERT) == len(entry.get()):
                if current_col < len(self.headers) - 1:  # Adjusted to include 'Target Type'
                    target_entry = self.towers[current_row][self.get_field_by_col(current_col + 1)]
                    target_entry.focus_set()
                    target_entry.icursor(0)

    def get_field_by_col(self, col):
        fields = ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                  'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                  'Slow %', 'Utility Boost']
        if col < len(fields):
            return fields[col]
        elif col == len(fields):  # Poison
            return 'Poison'
        elif col == len(fields) + 1:  # Target Type
            return 'Target Type'
        # Remove 'Z-Score', 'Percent Rank', 'Balance Status' as they are not GUI fields
        return None

    def format_number(self, num):
        if isinstance(num, float):
            if num >= 100:
                return str(int(round(num)))
            elif num >= 10:
                return f"{round(num,1):.1f}".rstrip('0').rstrip('.')
            else:
                return f"{round(num,2):.2f}".rstrip('0').rstrip('.')
        else:
            return str(num)

    def _calculate_all_internal(self):
        # Clear previous results
        self.result_text.configure(state=tk.NORMAL)
        self.result_text.delete("1.0", "end")
        self.result_text.configure(state=tk.DISABLED)

        # Step 1: Collect current race's data from the GUI
        selected_race = self.race_entry.get().strip()
        if not selected_race:
            messagebox.showerror("Calculation Error", "Please enter a race name.")
            return

        current_race_data = []
        for i, tower in enumerate(self.towers):
            # Check if essential fields are filled
            if not tower['Name'].get().strip() and not tower['Damage'].get().strip():
                continue  # Skip this tower if essential fields are empty
            try:
                tower_number = i + 1
                base_damage = float(tower['Damage'].get() or 0)
                dice = int(float(tower['Dice'].get() or 0))
                sides = int(float(tower['Sides'].get() or 0))
                cooldown = float(tower['Cooldown'].get() or 1)
                cooldown = cooldown if cooldown != 0 else 1
                range_val = int(float(tower['Range'].get() or 300))
                full_splash = int(float(tower['Full Splash'].get() or 0))
                medium_splash = int(float(tower['Med Splash'].get() or 0))
                small_splash = int(float(tower['Small Splash'].get() or 0))
                gold_cost = int(float(tower['Gold Cost'].get() or 1))
                gold_cost = gold_cost if gold_cost != 0 else 1
                spell_dps = float(tower['Spell DPS'].get() or 0)
                spell_dps_cooldown = float(tower['Spell DPS CD'].get() or 1)
                spell_dps_cooldown = spell_dps_cooldown if spell_dps_cooldown != 0 else 1
                poison = tower['Poison'].get()
                slow_percentage = float(tower['Slow %'].get() or 0)
                utility_boost = float(tower['Utility Boost'].get() or 1.0)
                utility_boost = utility_boost if utility_boost != 0 else 1.0
                target_type = tower['Target Type'].get()
                race = self.race_entry.get()

                # Append to current_race_data
                current_race_data.append({
                    'Name': tower['Name'].get(),
                    'Gold Cost': gold_cost,
                    'Damage': base_damage,
                    'Dice': dice,
                    'Sides': sides,
                    'Cooldown': cooldown,
                    'Range': range_val,
                    'Full Splash': full_splash,
                    'Med Splash': medium_splash,
                    'Small Splash': small_splash,
                    'Spell DPS': spell_dps,
                    'Spell DPS CD': spell_dps_cooldown,
                    'Slow %': slow_percentage,
                    'Utility Boost': utility_boost,
                    'Poison': poison,
                    'Target Type': target_type,
                    'Race': selected_race,
                    'Tower Number': tower_number
                })
            except ValueError as e:
                self.display_result(f"Tower {i+1}: Invalid input - {e}", color="red")

        # Step 2: Remove existing data for the selected race from imported_df
        if not self.imported_df.empty:
            self.imported_df = self.imported_df[self.imported_df['Race'] != selected_race]

        # Step 3: Append current race's data to imported_df
        if current_race_data:
            df_current_race = pd.DataFrame(current_race_data)
            self.imported_df = pd.concat([self.imported_df, df_current_race], ignore_index=True)

        # Collect data from all imported towers across all races
        all_tower_data = []
        if not self.imported_df.empty:
            for _, tower_row in self.imported_df.iterrows():
                try:
                    tower_number = int(tower_row.get('Tower Number', 0))
                    base_damage = float(tower_row.get('Damage', 0) or 0)
                    dice = int(float(tower_row.get('Dice', 0) or 0))
                    sides = int(float(tower_row.get('Sides', 0) or 0))
                    cooldown = float(tower_row.get('Cooldown', 1) or 1)
                    if cooldown == 0:
                        cooldown = 1
                    range_val = int(float(tower_row.get('Range', 300) or 300))
                    full_splash = int(float(tower_row.get('Full Splash', 0) or 0))
                    medium_splash = int(float(tower_row.get('Med Splash', 0) or 0))
                    small_splash = int(float(tower_row.get('Small Splash', 0) or 0))
                    gold_cost = int(float(tower_row.get('Gold Cost', 1) or 1))
                    if gold_cost == 0:
                        gold_cost = 1
                    spell_dps = float(tower_row.get('Spell DPS', 0) or 0)
                    spell_dps_cooldown = float(tower_row.get('Spell DPS CD', 1) or 1)
                    if spell_dps_cooldown == 0:
                        spell_dps_cooldown = 1
                    poison = tower_row.get('Poison', 0)
                    slow_percentage = float(tower_row.get('Slow %', 0) or 0)
                    utility_boost = float(tower_row.get('Utility Boost', 1.0) or 1.0)
                    if utility_boost == 0:
                        utility_boost = 1.0
                    target_type = tower_row.get('Target Type', 'All')
                    race = tower_row.get('Race', '')

                    total_dps, dps_per_gold = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, full_splash,
                        medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type=target_type, include_splash=True)

                    all_tower_data.append({
                        'Tower Number': tower_number,
                        'Total DPS': total_dps,
                        'DPS per Gold': dps_per_gold,
                        'Target Type': target_type,
                        'Race': race
                    })
                except ValueError:
                    continue

        # Perform statistical analysis for dynamic balance ranges
        df_all_towers = pd.DataFrame(all_tower_data)
        if not df_all_towers.empty:
            # Group by Tower Number and Target Type
            grouped = df_all_towers.groupby(['Tower Number', 'Target Type'])
            self.balance_ranges = {}
            self.global_dps_per_gold_ranges = {}
            self.global_raw_dps_ranges = {}
            for (tower_num, target_type), group in grouped:
                # Decide whether to ignore outliers
                if self.dynamic_comparison_var.get() and self.ignore_outliers_var.get():
                    # Exclude outliers using IQR
                    Q1 = group['DPS per Gold'].quantile(0.25)
                    Q3 = group['DPS per Gold'].quantile(0.75)
                    IQR = Q3 - Q1
                    filtered_group = group[(group['DPS per Gold'] >= Q1 - 1.5 * IQR) & (group['DPS per Gold'] <= Q3 + 1.5 * IQR)]
                    if filtered_group.empty:
                        filtered_group = group
                else:
                    filtered_group = group

                mean_dps_per_gold = filtered_group['DPS per Gold'].mean()
                std_dps_per_gold = filtered_group['DPS per Gold'].std(ddof=0)  # Population std
                mean_total_dps = filtered_group['Total DPS'].mean()
                std_total_dps = filtered_group['Total DPS'].std(ddof=0)

                # Handle cases with zero std deviation
                if std_dps_per_gold == 0:
                    std_dps_per_gold = mean_dps_per_gold * 0.1  # Assume 10% variation
                if std_total_dps == 0:
                    std_total_dps = mean_total_dps * 0.1

                # Define balance range as mean ± one standard deviation
                low_range = mean_dps_per_gold - std_dps_per_gold
                high_range = mean_dps_per_gold + std_dps_per_gold

                # Scaling factor inversely proportional to tower number
                scaling_factor = 1 / (tower_num ** 0.05)  # Implemented scaling_factor as per request
                low_range *= scaling_factor
                high_range *= scaling_factor

                self.balance_ranges[(tower_num, target_type)] = (low_range, high_range)
                self.global_dps_per_gold_ranges[(tower_num, target_type)] = (filtered_group['DPS per Gold'].min(), filtered_group['DPS per Gold'].max())
                self.global_raw_dps_ranges[(tower_num, target_type)] = (filtered_group['Total DPS'].min(), filtered_group['Total DPS'].max())

            # Calculate Z-Score and Percent Rank for each race, tower number, and target type
            def calculate_z_score(x):
                if len(x) > 1:
                    return stats.zscore(x, ddof=0)
                else:
                    return np.array([0])

            def calculate_percent_rank(x):
                if len(x) > 1:
                    return x.rank(pct=True) * 100
                else:
                    return np.array([50])

            df_all_towers['Z-Score'] = grouped['DPS per Gold'].transform(calculate_z_score)
            df_all_towers['Percent Rank'] = grouped['DPS per Gold'].transform(lambda x: x.rank(pct=True) * 100 if len(x) > 1 else np.full(len(x), 50))

        # Prepare data for the towers in the current race
        race_tower_data = []
        for i, tower in enumerate(self.towers):
            # Tower numbering starts from 1
            tower_number = i + 1
            # Check if essential fields are filled
            if not tower['Name'].get().strip() and not tower['Damage'].get().strip():
                continue  # Skip this tower if essential fields are empty
            try:
                base_damage = float(tower['Damage'].get() or 0)
                dice = int(float(tower['Dice'].get() or 0))
                sides = int(float(tower['Sides'].get() or 0))
                cooldown = float(tower['Cooldown'].get() or 1)  # Avoid division by zero
                if cooldown == 0:
                    cooldown = 1
                range_val = int(float(tower['Range'].get() or 300))
                full_splash = int(float(tower['Full Splash'].get() or 0))
                medium_splash = int(float(tower['Med Splash'].get() or 0))
                small_splash = int(float(tower['Small Splash'].get() or 0))
                gold_cost = int(float(tower['Gold Cost'].get() or 1))  # Avoid division by zero
                if gold_cost == 0:
                    gold_cost = 1
                spell_dps = float(tower['Spell DPS'].get() or 0)
                spell_dps_cooldown = float(tower['Spell DPS CD'].get() or 1)
                if spell_dps_cooldown == 0:
                    spell_dps_cooldown = 1
                poison = tower['Poison'].get()
                slow_percentage = float(tower['Slow %'].get() or 0)
                utility_boost = float(tower['Utility Boost'].get() or 1.0)
                if utility_boost == 0:
                    utility_boost = 1.0
                # Get the target type
                target_type = tower['Target Type'].get()
                race = self.race_entry.get()

                # Decide which balance ranges to use
                if self.dynamic_comparison_var.get():
                    # Use dynamic balance ranges
                    base_low, base_high = self.balance_ranges.get((tower_number, target_type), (0, 0))
                else:
                    # Use preset balance ranges
                    base_low, base_high = self.preset_balance_ranges.get(tower_number, (0, 0))

                # Get global ranges
                global_dps_per_gold_min, global_dps_per_gold_max = self.global_dps_per_gold_ranges.get((tower_number, target_type), (0, 0))
                global_raw_dps_min, global_raw_dps_max = self.global_raw_dps_ranges.get((tower_number, target_type), (0, 0))

                # Get tower name
                tower_name = tower['Name'].get()

                if target_type == 'All':
                    # Calculate total_dps and dps_per_gold as usual
                    total_dps, dps_per_gold = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, full_splash,
                        medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type=target_type, include_splash=True)

                    # Check if Z-Score exists for the tower in the selected race
                    z_score_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    # Only proceed if z_score_row is not empty
                    if not z_score_row.empty:
                        z_score = z_score_row.values[0]  # Get the first value
                    else:
                        z_score = 0  # Default to 0 if no result is found

                    # Check if Percent Rank exists for the tower in the selected race
                    percent_rank_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Percent Rank'
                    ]

                    # Only proceed if percent_rank_row is not empty
                    if not percent_rank_row.empty:
                        percent_rank = percent_rank_row.values[0]  # Get the first value
                    else:
                        percent_rank = 0  # Default to 0 if no result is found

                    # **Check balance with all conditions (Updated Call)**
                    balance_status = self.check_balance(dps_per_gold, base_low, base_high, z_score, percent_rank)

                    # Format numbers
                    dps_per_gold_str = self.format_number(dps_per_gold)
                    total_dps_str = self.format_number(total_dps)
                    balance_range_str = f"{self.format_number(base_low)} - {self.format_number(base_high)}"
                    global_dps_per_gold_str = f"{self.format_number(global_dps_per_gold_min)} - {self.format_number(global_dps_per_gold_max)}"
                    global_raw_dps_str = f"{self.format_number(global_raw_dps_min)} - {self.format_number(global_raw_dps_max)}"
                    z_score_str = f"{round(z_score, 2)}"

                    # **Round Percentile Rank to the nearest multiple of 5 (Updated Formatting)**
                    percent_rank_rounded = int(round(percent_rank / 5.0)) * 5
                    # Ensure the value is within 0-100%
                    percent_rank_rounded = max(0, min(percent_rank_rounded, 100))
                    percent_rank_str = f"{percent_rank_rounded}%"

                    # Prepare data for display
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name,
                        'DPS per Gold': dps_per_gold_str,
                        'Balance Status': balance_status,
                        'Balance Range': balance_range_str,
                        'Z-Score': z_score_str,          # Added
                        'Percent Rank': percent_rank_str, # Added
                        'Raw DPS': total_dps_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str
                    })

                elif target_type == 'Ground Splash':
                    # Primary Variant: Ground Splash with 1.5x 'All' balance range and splash damage
                    total_dps_ground, dps_per_gold_ground = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, full_splash,
                        medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type=target_type, include_splash=True)

                    # Adjust balance ranges (1.5x 'All' balance range)
                    adjusted_low_ground = base_low * 1.5
                    adjusted_high_ground = base_high * 1.5

                    # **Retrieve Z-Score and Percent Rank for Ground Splash**
                    z_score_ground_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_ground_row.empty:
                        z_score_ground = z_score_ground_row.values[0]
                    else:
                        z_score_ground = 0  # Default value if not found

                    percent_rank_ground_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Percent Rank'
                    ]

                    if not percent_rank_ground_row.empty:
                        percent_rank_ground = percent_rank_ground_row.values[0]
                    else:
                        percent_rank_ground = 0  # Default value if not found

                    # **Round Percentile Rank to the nearest multiple of 5**
                    percent_rank_ground_rounded = int(round(percent_rank_ground / 5.0)) * 5
                    percent_rank_ground_rounded = max(0, min(percent_rank_ground_rounded, 100))
                    percent_rank_ground_str = f"{percent_rank_ground_rounded}%"

                    # **Check balance with all conditions (Updated Call)**
                    balance_status_ground = self.check_balance(dps_per_gold_ground, adjusted_low_ground, adjusted_high_ground, z_score_ground, percent_rank_ground)

                    # Format numbers
                    dps_per_gold_ground_str = self.format_number(dps_per_gold_ground)
                    total_dps_ground_str = self.format_number(total_dps_ground)
                    balance_range_ground_str = f"{self.format_number(adjusted_low_ground)} - {self.format_number(adjusted_high_ground)}"
                    global_dps_per_gold_str = f"{self.format_number(global_dps_per_gold_min)} - {self.format_number(global_dps_per_gold_max)}"
                    global_raw_dps_str = f"{self.format_number(global_raw_dps_min)} - {self.format_number(global_raw_dps_max)}"

                    # Retrieve Z-Score string
                    z_score_ground_str = f"{round(z_score_ground, 2)}"

                    # Prepare data for display (Ground Splash)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Ground Splash)",
                        'DPS per Gold': dps_per_gold_ground_str,
                        'Balance Status': balance_status_ground,
                        'Balance Range': balance_range_ground_str,
                        'Z-Score': z_score_ground_str,          # Added
                        'Percent Rank': percent_rank_ground_str, # Added
                        'Raw DPS': total_dps_ground_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str
                    })

                    # Secondary Variant: Air with 0.5x 'All' balance range and no splash damage
                    total_dps_air, dps_per_gold_air = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, 0, 0, 0, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type='Air', include_splash=False)

                    # Adjust balance ranges (0.5x 'All' balance range)
                    adjusted_low_air = base_low * 0.5
                    adjusted_high_air = base_high * 0.5

                    # **Retrieve Z-Score and Percent Rank for Air Variant**
                    z_score_air_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Air') &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_air_row.empty:
                        z_score_air = z_score_air_row.values[0]
                    else:
                        z_score_air = 0  # Default value if not found

                    percent_rank_air_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Air') &
                        (df_all_towers['Race'] == selected_race),
                        'Percent Rank'
                    ]

                    if not percent_rank_air_row.empty:
                        percent_rank_air = percent_rank_air_row.values[0]
                    else:
                        percent_rank_air = 0  # Default value if not found

                    # **Round Percentile Rank to the nearest multiple of 5**
                    percent_rank_air_rounded = int(round(percent_rank_air / 5.0)) * 5
                    percent_rank_air_rounded = max(0, min(percent_rank_air_rounded, 100))
                    percent_rank_air_str = f"{percent_rank_air_rounded}%"

                    # **Check balance with all conditions (Updated Call)**
                    balance_status_air = self.check_balance(dps_per_gold_air, adjusted_low_air, adjusted_high_air, z_score_air, percent_rank_air)

                    # Format numbers
                    dps_per_gold_air_str = self.format_number(dps_per_gold_air)
                    total_dps_air_str = self.format_number(total_dps_air)
                    balance_range_air_str = f"{self.format_number(adjusted_low_air)} - {self.format_number(adjusted_high_air)}"

                    # Retrieve Z-Score string
                    z_score_air_str = f"{round(z_score_air, 2)}"

                    # Prepare data for display (Air Variant)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Air)",
                        'DPS per Gold': dps_per_gold_air_str,
                        'Balance Status': balance_status_air,
                        'Balance Range': balance_range_air_str,
                        'Z-Score': z_score_air_str,          # Added
                        'Percent Rank': percent_rank_air_str, # Added
                        'Raw DPS': total_dps_air_str,
                        'Target': 'Air',
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str
                    })

                elif target_type == 'Air Splash':
                    # Handle "Air Splash" Target Type
                    # Primary Variant: Air Splash with 1.5x 'All' balance range and splash damage
                    total_dps_air_splash, dps_per_gold_air_splash = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, full_splash,
                        medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type=target_type, include_splash=True)

                    # Adjust balance ranges (1.5x 'All' balance range)
                    adjusted_low_air_splash = base_low * 1.5
                    adjusted_high_air_splash = base_high * 1.5

                    # **Retrieve Z-Score and Percent Rank for Air Splash**
                    z_score_air_splash_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_air_splash_row.empty:
                        z_score_air_splash = z_score_air_splash_row.values[0]
                    else:
                        z_score_air_splash = 0  # Default value if not found

                    percent_rank_air_splash_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Percent Rank'
                    ]

                    if not percent_rank_air_splash_row.empty:
                        percent_rank_air_splash = percent_rank_air_splash_row.values[0]
                    else:
                        percent_rank_air_splash = 0  # Default value if not found

                    # **Round Percentile Rank to the nearest multiple of 5**
                    percent_rank_air_splash_rounded = int(round(percent_rank_air_splash / 5.0)) * 5
                    percent_rank_air_splash_rounded = max(0, min(percent_rank_air_splash_rounded, 100))
                    percent_rank_air_splash_str = f"{percent_rank_air_splash_rounded}%"

                    # **Check balance with all conditions (Updated Call)**
                    balance_status_air_splash = self.check_balance(dps_per_gold_air_splash, adjusted_low_air_splash, adjusted_high_air_splash, z_score_air_splash, percent_rank_air_splash)

                    # Format numbers
                    dps_per_gold_air_splash_str = self.format_number(dps_per_gold_air_splash)
                    total_dps_air_splash_str = self.format_number(total_dps_air_splash)
                    balance_range_air_splash_str = f"{self.format_number(adjusted_low_air_splash)} - {self.format_number(adjusted_high_air_splash)}"
                    global_dps_per_gold_str = f"{self.format_number(global_dps_per_gold_min)} - {self.format_number(global_dps_per_gold_max)}"
                    global_raw_dps_str = f"{self.format_number(global_raw_dps_min)} - {self.format_number(global_raw_dps_max)}"

                    # Retrieve Z-Score string
                    z_score_air_splash_str = f"{round(z_score_air_splash, 2)}"

                    # Prepare data for display (Air Splash)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Air Splash)",
                        'DPS per Gold': dps_per_gold_air_splash_str,
                        'Balance Status': balance_status_air_splash,
                        'Balance Range': balance_range_air_splash_str,
                        'Z-Score': z_score_air_splash_str,          # Added
                        'Percent Rank': percent_rank_air_splash_str, # Added
                        'Raw DPS': total_dps_air_splash_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str
                    })

                    # Secondary Variant: Ground (Ignoring Splash Damage)
                    total_dps_ground_variant, dps_per_gold_ground_variant = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, 0, 0, 0, gold_cost,
                        spell_dps=spell_dps, spell_dps_cooldown=spell_dps_cooldown,
                        poison=poison, utility_boost=utility_boost,
                        slow_percentage=slow_percentage, target_type='Ground',
                        include_splash=False)

                    # Adjust balance ranges (0.5x 'All' balance range)
                    adjusted_low_ground_variant = base_low * 0.5
                    adjusted_high_ground_variant = base_high * 0.5

                    # **Retrieve Z-Score and Percent Rank for Ground Variant**
                    z_score_ground_variant_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Ground') &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_ground_variant_row.empty:
                        z_score_ground_variant = z_score_ground_variant_row.values[0]
                    else:
                        z_score_ground_variant = 0  # Default value if not found

                    percent_rank_ground_variant_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Ground') &
                        (df_all_towers['Race'] == selected_race),
                        'Percent Rank'
                    ]

                    if not percent_rank_ground_variant_row.empty:
                        percent_rank_ground_variant = percent_rank_ground_variant_row.values[0]
                    else:
                        percent_rank_ground_variant = 0  # Default value if not found

                    # **Round Percentile Rank to the nearest multiple of 5**
                    percent_rank_ground_variant_rounded = int(round(percent_rank_ground_variant / 5.0)) * 5
                    percent_rank_ground_variant_rounded = max(0, min(percent_rank_ground_variant_rounded, 100))
                    percent_rank_ground_variant_str = f"{percent_rank_ground_variant_rounded}%"

                    # **Check balance with all conditions (Updated Call)**
                    balance_status_ground_variant = self.check_balance(dps_per_gold_ground_variant, adjusted_low_ground_variant, adjusted_high_ground_variant, z_score_ground_variant, percent_rank_ground_variant)

                    # Format numbers
                    dps_per_gold_ground_variant_str = self.format_number(dps_per_gold_ground_variant)
                    total_dps_ground_variant_str = self.format_number(total_dps_ground_variant)
                    balance_range_ground_variant_str = f"{self.format_number(adjusted_low_ground_variant)} - {self.format_number(adjusted_high_ground_variant)}"

                    # Retrieve Z-Score string
                    z_score_ground_variant_str = f"{round(z_score_ground_variant, 2)}"

                    # Prepare data for display (Ground Variant)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Ground)",
                        'DPS per Gold': dps_per_gold_ground_variant_str,
                        'Balance Status': balance_status_ground_variant,
                        'Balance Range': balance_range_ground_variant_str,
                        'Z-Score': z_score_ground_variant_str,          # Added
                        'Percent Rank': percent_rank_ground_variant_str, # Added
                        'Raw DPS': total_dps_ground_variant_str,
                        'Target': 'Ground',
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str
                    })

                else:
                    # Handle unexpected target types
                    continue

            except ValueError as e:
                self.display_result(f"Tower {tower_number}: Invalid - {e}", color="red")

        # Adjust format_string to reflect the new order and alignment
        format_string = "{:<6} {:<30} {:<12} {:<15} {:<15} {:<10} {:<10} {:<12} {:<15} {:<15} {:<15}"

        # Insert the header at the beginning of the result box
        header = format_string.format(
            "Tower", "Name", "DPS/Gold", "Status", "Balance Range", "Z-Score", "Rank", "Raw DPS",
            "Target", "Global DPS/Gold", "Global Raw DPS"
        )
        self.display_result(header, color="#00FFFF", bold=True)
        self.display_result("-" * 160, color="black")

        # Display the results
        for data in race_tower_data:
            # Determine the color based on Balance Status
            if data['Balance Status'] == "Balanced":
                color = "green"
            elif data['Balance Status'] in ["Underpowered", "Overpowered"]:
                color = "red"
            else:
                color = "yellow"  # For outliers or undefined statuses

            result_line = format_string.format(
                data['Tower Number'],
                data['Tower Name'],
                data['DPS per Gold'],
                data['Balance Status'],
                data['Balance Range'],
                data['Z-Score'],
                data['Percent Rank'],
                data['Raw DPS'],
                data['Target'],
                data['Global DPS per Gold'],
                data['Global Raw DPS']
            )
            self.display_result(result_line, color=color)

        # Append Outlier Section with Race context
        outliers_low = df_all_towers[df_all_towers['DPS per Gold'] < df_all_towers.groupby(['Tower Number', 'Target Type'])['DPS per Gold'].transform(lambda x: x.quantile(0.05))]
        outliers_high = df_all_towers[df_all_towers['DPS per Gold'] > df_all_towers.groupby(['Tower Number', 'Target Type'])['DPS per Gold'].transform(lambda x: x.quantile(0.95))]

        # Create a set of (Tower Number, Target Type) tuples that are outliers
        outliers_low_set = set(zip(outliers_low['Tower Number'], outliers_low['Target Type'], outliers_low['Race']))
        outliers_high_set = set(zip(outliers_high['Tower Number'], outliers_high['Target Type'], outliers_high['Race']))
        all_outliers = outliers_low_set | outliers_high_set

        if not outliers_low.empty or not outliers_high.empty:
            self.display_result("\n" + "="*160, color="black")
            self.display_result("Outlier Analysis:", color="#FFFF00", bold=True)

            # Display low-end outliers
            if not outliers_low.empty:
                self.display_result("\nLow-End Outliers:", color="red", bold=True)
                for _, row in outliers_low.iterrows():
                    tower_info = f"Tower {row['Tower Number']} ("
                    race_info = f"{row['Race']}"
                    target_type = f", {row['Target Type']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_info = f" (Balance Range: {self.format_number(balance_range[0])} - {self.format_number(balance_range[1])})"
                    
                    # Define segments with desired colors
                    segments = [
                        (tower_info, "#4DA6FF", True),       # Tower Info in Dark Turquoise
                        (race_info, "#FFD966", True),        # Race Name in Light Blue
                        (target_type, "#00CED1"),      # Target Type in Dark Turquoise
                        (dps_gold, "red" if row['DPS per Gold'] < balance_range[0] else "green"),  # DPS/Gold in Red or Green
                        (balance_info, "#A0A0A0")      # Balance Range in Light Green
                    ]
                    self.display_colored_line(segments)

            # Display high-end outliers
            if not outliers_high.empty:
                self.display_result("\nHigh-End Outliers:", color="red", bold=True)
                for _, row in outliers_high.iterrows():
                    tower_info = f"Tower {row['Tower Number']} ("
                    race_info = f"{row['Race']}"
                    target_type = f", {row['Target Type']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_info = f" (Balance Range: {self.format_number(balance_range[0])} - {self.format_number(balance_range[1])})"
                    
                    # Define segments with desired colors
                    segments = [
                        (tower_info, "#4DA6FF", True),       # Tower Info in Dark Turquoise
                        (race_info, "#FFD966", True),        # Race Name in Light Blue
                        (target_type, "#00CED1"),      # Target Type in Dark Turquoise
                        (dps_gold, "red" if row['DPS per Gold'] > balance_range[1] else "green"),  # DPS/Gold in Red or Green
                        (balance_info, "#A0A0A0")      # Balance Range in Light Green
                    ]
                    self.display_colored_line(segments)

        # Step 2: Update color-coding logic based on outlier status
        for data in race_tower_data:
            tower_number = data['Tower Number']
            target_type = data['Target']
            balance_status = data['Balance Status']
            is_outlier = (tower_number, target_type, race) in all_outliers  # Check if tower is an outlier

            # Get the tower number label for the respective tower
            tower_label = self.towers[tower_number - 1]['No.']
            
            # Set color based on outlier flag and balance status
            if is_outlier:
                color = "#FFFF00"  # Yellow for outliers
            elif balance_status == "Balanced":
                color = "#00D1A0"  # Green for Balanced
            elif balance_status in ["Underpowered", "Overpowered"]:
                color = "#FF4C4C"  # Red for Underpowered or Overpowered
            else:
                color = "white"  # Default color for undefined statuses

            # Update the tower number label color and make it bold
            tower_label.configure(text_color=color, font=("Arial", 13, "bold"))


            # After inserting text, scroll back to the top
            self.result_text.yview_moveto(0)
            self.result_text.configure(state=tk.DISABLED)

            # Initialize outlier_analysis_segments
            self.outlier_analysis_segments = []
            self.outlier_analysis_segments.append([("Outlier Analysis:\n", "#FFFF00", True)])  # Use a list of segments for each line

            # Low-End Outliers
            if not outliers_low.empty:
                self.outlier_analysis_segments.append([("\nLow-End Outliers:\n", "red", True)])
                for _, row in outliers_low.iterrows():
                    tower_info = f"Tower {row['Tower Number']} ("
                    race_info = f"{row['Race']}"
                    target_type = f", {row['Target Type']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_info = f" (Balance Range: {self.format_number(balance_range[0])} - {self.format_number(balance_range[1])})\n"

                    # Define segments with desired colors
                    segments = [
                        (tower_info, "#4DA6FF", True),       # Tower Info in Dark Turquoise, bold
                        (race_info, "#FFD966", True),        # Race Name in Light Blue, bold
                        (target_type, "#00CED1"),            # Target Type in Dark Turquoise
                        (dps_gold, "red" if row['DPS per Gold'] < balance_range[0] else "green"),  # DPS/Gold in Red or Green
                        (balance_info, "#A0A0A0")            # Balance Range in Light Green
                    ]
                    self.outlier_analysis_segments.append(segments)

            # High-End Outliers
            if not outliers_high.empty:
                self.outlier_analysis_segments.append([("\nHigh-End Outliers:\n", "red", True)])
                for _, row in outliers_high.iterrows():
                    tower_info = f"Tower {row['Tower Number']} ("
                    race_info = f"{row['Race']}"
                    target_type = f", {row['Target Type']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_info = f" (Balance Range: {self.format_number(balance_range[0])} - {self.format_number(balance_range[1])})\n"

                    # Define segments with desired colors
                    segments = [
                        (tower_info, "#4DA6FF", True),       # Tower Info in Dark Turquoise, bold
                        (race_info, "#FFD966", True),        # Race Name in Light Blue, bold
                        (target_type, "#00CED1"),            # Target Type in Dark Turquoise
                        (dps_gold, "red" if row['DPS per Gold'] > balance_range[1] else "green"),  # DPS/Gold in Red or Green
                        (balance_info, "#A0A0A0")            # Balance Range in Light Green
                    ]
                    self.outlier_analysis_segments.append(segments)

            # Now compute Race Difficulty Levels using weighted factors
            if not self.imported_df.empty:
                df_all_towers = self.imported_df.copy()
                df_all_towers['Gold Cost'] = df_all_towers['Gold Cost'].astype(float)
                df_all_towers['Range'] = df_all_towers['Range'].astype(float)
                df_all_towers['Utility Boost'] = df_all_towers['Utility Boost'].astype(float)
                df_all_towers['Full Splash'] = df_all_towers['Full Splash'].astype(float)
                df_all_towers['Med Splash'] = df_all_towers['Med Splash'].astype(float)
                df_all_towers['Small Splash'] = df_all_towers['Small Splash'].astype(float)
                df_all_towers['Slow %'] = df_all_towers['Slow %'].astype(float)
                df_all_towers['Spell DPS'] = df_all_towers['Spell DPS'].astype(float)
            
                # Calculate Total DPS and DPS per Gold
                df_all_towers['Total DPS'] = df_all_towers.apply(lambda row: self.calculate_dps_per_gold(
                    float(row.get('Damage', 0) or 0),
                    int(float(row.get('Dice', 0) if pd.notnull(row.get('Dice')) else 0)),
                    int(float(row.get('Sides', 0) if pd.notnull(row.get('Sides')) else 0)),
                    float(row.get('Cooldown', 1) or 1),
                    int(float(row.get('Range', 300) if pd.notnull(row.get('Range')) else 300)),
                    int(float(row.get('Full Splash', 0) if pd.notnull(row.get('Full Splash')) else 0)),
                    int(float(row.get('Med Splash', 0) if pd.notnull(row.get('Med Splash')) else 0)),
                    int(float(row.get('Small Splash', 0) if pd.notnull(row.get('Small Splash')) else 0)),
                    float(row.get('Gold Cost', 1) or 1),
                    spell_dps=float(row.get('Spell DPS', 0) or 0),
                    spell_dps_cooldown=float(row.get('Spell DPS CD', 1) or 1),
                    poison=row.get('Poison', 0),
                    utility_boost=float(row.get('Utility Boost', 1.0) if pd.notnull(row.get('Utility Boost')) else 1.0),
                    slow_percentage=float(row.get('Slow %', 0) if pd.notnull(row.get('Slow %')) else 0),
                    target_type=row.get('Target Type', 'All'),
                    include_splash=True
                )[0], axis=1)
                df_all_towers['DPS per Gold'] = df_all_towers['Total DPS'] / df_all_towers['Gold Cost'] * 100

                # Compute 'Splash Factor' as a sum of splash radii
                df_all_towers['Splash'] = df_all_towers['Full Splash'] + df_all_towers['Med Splash'] + df_all_towers['Small Splash']

                # Now, for each factor, normalize the values between 0 and 1
                factors = ['DPS per Gold', 'Total DPS', 'Range', 'Utility Boost', 'Splash', 'Slow %', 'Spell DPS']
                for factor in factors:
                    min_value = df_all_towers[factor].min()
                    max_value = df_all_towers[factor].max()
                    if max_value - min_value == 0:
                        df_all_towers[factor + '_Norm'] = 0.5  # Default to 0.5 if no variation
                    else:
                        df_all_towers[factor + '_Norm'] = (df_all_towers[factor] - min_value) / (max_value - min_value)
                
                # Define weights for each factor
                weights = {
                    'DPS per Gold_Norm': 0.2,
                    'Total DPS_Norm': 0.2,
                    'Range_Norm': 0.2,
                    'Utility Boost_Norm': 0.1,
                    'Splash_Norm': 0.2,
                    'Slow %_Norm': 0.1,
                }
                
                # Compute weighted score for each tower
                df_all_towers['Weighted Score'] = 0
                for factor, weight in weights.items():
                    df_all_towers['Weighted Score'] += df_all_towers[factor] * weight

                # Now compute average score per race
                race_difficulty = df_all_towers.groupby('Race')['Weighted Score'].mean().reset_index()

                # Normalize the average scores to a scale of 1 to 10
                min_score = race_difficulty['Weighted Score'].min()
                max_score = race_difficulty['Weighted Score'].max()

                def map_difficulty(score):
                    if max_score - min_score == 0:
                        return 5  # Default difficulty if no variation
                    else:
                        normalized = (score - min_score) / (max_score - min_score)
                        inverted_score = 1 - normalized # adjusts difficulty from the perspective of the player instead of the opponent
                        return int(round(inverted_score * 9 + 1))  # Map to 1-10 scale

                race_difficulty['Difficulty'] = race_difficulty['Weighted Score'].apply(map_difficulty)

                # Append Race Difficulty Levels to outlier_analysis_segments
                self.outlier_analysis_segments.append([("\nRace Difficulty Levels:\n", "#FFFF00", True)])  # Yellow color, bold

                # Sort the races alphabetically
                race_difficulty = race_difficulty.sort_values('Race')

                for _, row in race_difficulty.iterrows():
                    race_name = row['Race']
                    difficulty = row['Difficulty']
                    difficulty_str = f"Difficulty Level {difficulty}"

                    # Determine color for difficulty level
                    if 1 <= difficulty <= 3:
                        difficulty_color = "green"
                    elif 4 <= difficulty <= 7:
                        difficulty_color = "orange"
                    elif 8 <= difficulty <= 10:
                        difficulty_color = "red"
                    else:
                        difficulty_color = "white"  # Default color

                    # Build the segments
                    segments = [
                        (race_name, "#FFD966", True),  # Race Name in #FFD966, bold
                        (": ", "white"),
                        (difficulty_str, difficulty_color),
                        ("\n", "white")
                    ]
                    self.outlier_analysis_segments.append(segments)
            else:
                # If imported_df is empty, display message
                self.outlier_analysis_segments.append([("Import data or add races to view outlier analysis and race difficulty levels.\n", "white")])

            self.changes_report = self.generate_changes_report()
            #self.update_view_changes_tab()
            #self.update_analysis_window()
            try:
                if hasattr(self, 'analysis_text') and self.analysis_text.winfo_exists() and self.analysis_text.winfo_ismapped():
                    self.update_analysis_window()
            except tk.TclError:
                # Widget no longer exists, skip updating
                pass

            # Safely check if the View Changes tab is open and update if necessary
            try:
                if hasattr(self, 'view_changes_text') and self.view_changes_text.winfo_exists() and self.view_changes_text.winfo_ismapped():
                    # Regenerate the changes report if needed
                    self.changes_report = self.generate_changes_report()
                    self.update_view_changes_tab()
            except tk.TclError:
                # Widget no longer exists, skip updating
                pass

            self.calculate_all_after_id = None

    def calculate_all(self):
        if self.calculate_all_after_id:
                self.root.after_cancel(self.calculate_all_after_id)
        self.calculate_all_after_id = self.root.after(200, self._calculate_all_internal)

    def run_calculate_all(self):
        # Ensure calculate all runs on the main thread using after timer. Prevents TKinter issues
        self.root.after(0, self.calculate_all)

    def display_colored_line(self, segments):
        """
        Inserts a line into the result_text with multiple colored segments, with optional bold styling.

        Parameters:
        - segments (list of tuples): Each tuple contains (text, color, bold).
        """
        # Enable the text widget to insert content
        self.result_text.configure(state=tk.NORMAL)
        
        # Insert each segment with its respective color and bold option
        for segment in segments:
            if len(segment) == 3:
                text, color, bold = segment
            else:
                text, color = segment
                bold = False
            tag = color
            if bold:
                tag += "_bold"
            if tag not in self.result_text.tag_names():
                # Define a new tag with the specified foreground color and bold option
                font_style = ("Consolas", 11, "bold") if bold else ("Consolas", 11)
                self.result_text.tag_configure(tag, foreground=color, font=font_style)
            
            self.result_text.insert("end", text, tag)
        
        # Insert a newline at the end of the line
        self.result_text.insert("end", "\n")
        
        # Disable the text widget to make it read-only
        self.result_text.configure(state=tk.DISABLED)




    def display_result(self, text, color="black", bold=False):
        """
        Helper method to display text in the result_text with optional color and bold styling.
        """
        # Enable the text widget to insert content
        self.result_text.configure(state=tk.NORMAL)
        
        # Define the tag based on color and boldness
        tag = color
        if bold:
            tag += "_bold"
            if tag not in self.result_text.tag_names():
                self.result_text.tag_configure(tag, foreground=color, font=("Consolas", 11, "bold"))
        else:
            if tag not in self.result_text.tag_names():
                self.result_text.tag_configure(tag, foreground=color, font=("Consolas", 11))
        
        # Insert the text with the defined tag
        self.result_text.insert("end", text + "\n", tag)
        
        # Scroll to the end to show the latest entry
        self.result_text.see("end")
        
        # Disable the text widget to make it read-only
        self.result_text.configure(state=tk.DISABLED)



    def check_balance(self, dps_per_gold, low, high, z_score, percentile_rank):
        """
        Determines the balance status of a tower based on DPS/Gold, Z-Score, and Percentile Rank.

        Parameters:
        - dps_per_gold (float): The DPS per Gold value of the tower.
        - low (float): The lower bound of the balanced DPS/Gold range.
        - high (float): The upper bound of the balanced DPS/Gold range.
        - z_score (float): The Z-Score of the tower's DPS/Gold.
        - percentile_rank (float): The Percentile Rank of the tower's DPS/Gold.

        Returns:
        - str: "Balanced", "Underpowered", or "Overpowered".
        """
        if (low <= dps_per_gold <= high) and (-1 <= z_score <= 1) and (40 <= percentile_rank <= 60):
            return "Balanced"
        elif dps_per_gold < low or percentile_rank < 40:
            return "Underpowered"
        else:
            return "Overpowered"

    def export_data(self):
        # Ask the user where to save the file
        file_path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files", "*.csv"), ("All files", "*.*")])
        
        if not file_path:
            return  # Exit if no file path is selected

        # Check if there is data to export
        if self.imported_df.empty:
            messagebox.showerror("Export Error", "No data to export.")
            return

        # Save all races in the imported DataFrame to a CSV file
        try:
            # Saving the DataFrame to the specified CSV file path
            self.imported_df.to_csv(file_path, index=False)
            messagebox.showinfo("Export Successful", f"All races have been exported to {file_path}.")
        except Exception as e:
            messagebox.showerror("Export Error", f"An error occurred during export: {e}")




    def load_races_sequentially(self, races, index=0, total=0):
        """
        Loads races one by one, updating the importing message accordingly.
        
        Parameters:
        - races (list): List of race names to load.
        - index (int): Current index in the races list.
        - total (int): Total number of races to load.
        """
        if index < total:
            race = races[index]
            # Update dynamic label with current race
            if self.importing_message_label:
                self.importing_message_label.configure(text=f"Loading race {index + 1} of {total}: {race}")
            # Load race (Implement your actual loading logic here)
            self.on_race_selected(race)
            # Schedule next race loading after a short delay (e.g., 1ms)
            self.root.after(1, lambda: self.load_races_sequentially(races, index + 1, total))
        else:
            # Loading complete
            self.hide_importing_message()
            self.show_centered_message("All races loaded successfully!")
            # Automatically select the first race in the Combobox
            if races:
                first_race = races[0]
                self.race_combobox.set(first_race)
                self.on_race_selected(first_race)




    def import_data(self):
        """
        Imports race data from an Excel or CSV file, updates the race combobox,
        and sequentially loads all races with a loading message displayed during the process.
        """
        file_path = ctk.filedialog.askopenfilename(
            defaultextension=".xlsx",
            filetypes=[("Excel and CSV Files", "*.xlsx;*.csv"), ("All Files", "*.*")]
        )
        if not file_path:
            return

        # Determine file extension and load accordingly
        try:
            if file_path.endswith('.xlsx'):
                # Specify engine='openpyxl' for .xlsx files
                df = pd.read_excel(file_path, engine='openpyxl')
            elif file_path.endswith('.csv'):
                df = pd.read_csv(file_path)
            else:
                messagebox.showerror("Import Error", "Unsupported file format. Please select an Excel or CSV file.")
                return
        except Exception as e:
            messagebox.showerror("Import Error", f"An error occurred while reading the file: {e}")
            return

        if 'Race' not in df.columns:
            messagebox.showerror("Import Error", "No 'Race' column found in the data.")
            return

        # Clean 'Race' column
        df['Race'] = df['Race'].astype(str).str.strip()

        self.imported_df = df.copy()  # Working DataFrame for temporary changes
        self.original_imported_df = df.copy()  # Preserve original data

        # Get unique races and sort them alphabetically
        races = sorted(df['Race'].dropna().unique().tolist())
        if not races:
            messagebox.showerror("Import Error", "No races found in the data.")
            return

        # Update Combobox values
        self.race_combobox.configure(values=races)

        if races:
            # Show the importing message with dynamic updates
            self.show_importing_message("Loading races...")
            # Ensure the importing window is rendered before starting race loading
            self.root.update_idletasks()
            self.importing_window.update()
            # Start loading races sequentially
            self.load_races_sequentially(races, total=len(races))
        else:
            self.race_combobox.set('')  # Clear selection if no races found

        # Removed self.show_centered_message("Data Imported Successfully") as it's handled in load_races_sequentially
        self.calculate_all()  # Ensure calculations are performed after importing



    def quick_save(self):
        if self.imported_file_path:
            self.imported_df.to_excel(self.imported_file_path, index=False)
            self.show_centered_message("Data Successfully Saved")
        else:
            messagebox.showerror("Quick Save Error", "No file imported to save changes.")

    def save_temporary_backup(self):
        data = []
        for i, tower in enumerate(self.towers):
            if not tower['Name'].get().strip() and not tower['Damage'].get().strip():
                continue  # Skip this tower if essential fields are empty

            row = {
                'Name': tower['Name'].get() or '0',
                'Gold Cost': tower['Gold Cost'].get() or '0',
                'Damage': tower['Damage'].get() or '0',
                'Dice': tower['Dice'].get() or '0',
                'Sides': tower['Sides'].get() or '0',
                'Cooldown': tower['Cooldown'].get() or '0',
                'Range': tower['Range'].get() or '0',
                'Full Splash': tower['Full Splash'].get() or '0',
                'Med Splash': tower['Med Splash'].get() or '0',
                'Small Splash': tower['Small Splash'].get() or '0',
                'Spell DPS': tower['Spell DPS'].get() or '0',
                'Spell DPS CD': tower['Spell DPS CD'].get() or '0',
                'Slow %': tower['Slow %'].get() or '0',
                'Utility Boost': tower['Utility Boost'].get() or '0',
                'Poison': tower['Poison'].get(),
                'Target Type': tower['Target Type'].get(),
                'Z-Score': tower.get('Z-Score', ctk.StringVar()).get(),          # Updated
                'Percent Rank': tower.get('Percent Rank', ctk.StringVar()).get(), # Updated
                'Balance Status': tower.get('Balance Status', ctk.StringVar()).get(), # Updated
                'Race': self.race_entry.get(),
                'Tower Number': i+1
            }
            data.append(row)

        if data:
            temp_df = pd.DataFrame(data)
            temp_df.to_csv('temp_backup.csv', index=False)

    def save_current_race_data(self):
        # Collect current GUI data
        current_race_data = []
        selected_race = self.race_entry.get().strip()
        for i, tower in enumerate(self.towers):
            # Check if essential fields are filled
            if not tower['Name'].get().strip() and not tower['Damage'].get().strip():
                continue  # Skip this tower if essential fields are empty
            try:
                tower_number = i + 1
                base_damage = float(tower['Damage'].get() or 0)
                dice = int(float(tower['Dice'].get() or 0))
                sides = int(float(tower['Sides'].get() or 0))
                cooldown = float(tower['Cooldown'].get() or 1)
                cooldown = cooldown if cooldown != 0 else 1
                range_val = int(float(tower['Range'].get() or 300))
                full_splash = int(float(tower['Full Splash'].get() or 0))
                medium_splash = int(float(tower['Med Splash'].get() or 0))
                small_splash = int(float(tower['Small Splash'].get() or 0))
                gold_cost = int(float(tower['Gold Cost'].get() or 1))
                gold_cost = gold_cost if gold_cost != 0 else 1
                spell_dps = float(tower['Spell DPS'].get() or 0)
                spell_dps_cooldown = float(tower['Spell DPS CD'].get() or 1)
                spell_dps_cooldown = spell_dps_cooldown if spell_dps_cooldown != 0 else 1
                poison = tower['Poison'].get()
                slow_percentage = float(tower['Slow %'].get() or 0)
                utility_boost = float(tower['Utility Boost'].get() or 1.0)
                utility_boost = utility_boost if utility_boost != 0 else 1.0
                target_type = tower['Target Type'].get()

                current_race_data.append({
                    'Name': tower['Name'].get(),
                    'Gold Cost': gold_cost,
                    'Damage': base_damage,
                    'Dice': dice,
                    'Sides': sides,
                    'Cooldown': cooldown,
                    'Range': range_val,
                    'Full Splash': full_splash,
                    'Med Splash': medium_splash,
                    'Small Splash': small_splash,
                    'Spell DPS': spell_dps,
                    'Spell DPS CD': spell_dps_cooldown,
                    'Slow %': slow_percentage,
                    'Utility Boost': utility_boost,
                    'Poison': poison,
                    'Target Type': target_type,
                    'Race': selected_race,
                    'Tower Number': tower_number
                })
            except ValueError as e:
                self.display_result(f"Tower {i+1}: Invalid input - {e}", color="red")

        # Remove existing data for the selected race from imported_df
        if not self.imported_df.empty:
            self.imported_df = self.imported_df[self.imported_df['Race'] != selected_race]

        # Append current race's data to imported_df
        if current_race_data:
            df_current_race = pd.DataFrame(current_race_data)
            self.imported_df = pd.concat([self.imported_df, df_current_race], ignore_index=True)


    def on_race_selected(self, event):
        """
        Handles the event when a race is selected from the combobox.
        Updates the race entry field, populates tower data, and triggers calculations.
        
        Parameters:
        - event (str): The selected race name from the combobox.
        """
        try:
            selected_race = event.strip()  # Correctly assign the stripped event to selected_race
        except AttributeError:
            # If event is not a string, handle the error
            messagebox.showerror("Error", "Invalid race selection.")
            return

        #print(f"Selected Race: '{selected_race}'")  # Debugging
        self.save_current_race_data()

        # Update race_entry
        self.race_entry.configure(state='normal')
        self.race_entry.delete(0, ctk.END)
        self.race_entry.insert(0, selected_race)
        self.race_entry.configure(state='readonly')

        # Check if imported_df is empty or doesn't contain 'Race' column
        if self.imported_df.empty or 'Race' not in self.imported_df.columns:
            messagebox.showerror("Error", "No data available for the selected race.")
            print("imported_df is empty or missing 'Race' column.")
            return

        # Filter the dataframe for the selected race
        df_filtered = self.imported_df[self.imported_df['Race'] == selected_race]
        #print(f"Filtered DataFrame for race '{selected_race}':\n{df_filtered}")  # Debugging

        if df_filtered.empty:
            messagebox.showinfo("No Data", f"No tower data found for race '{selected_race}'.")
            print(f"No data found for race '{selected_race}'.")
            return

        # Populate towers
        self.populate_towers_from_df(df_filtered)

        # Automatically run calculation
        self.calculate_all()



    def populate_towers_from_df(self, df):
        # Clear the existing towers
        for tower in self.towers:
            tower['row_frame'].destroy()
        self.towers.clear()

        # Remove existing towers from the grid
        for widget in self.towers_frame.winfo_children():
            widget.destroy()

        # Recreate towers
        # Ensure 'Tower Number' is integer
        df.loc[:, 'Tower Number'] = df['Tower Number'].astype(int)
        df = df.sort_values('Tower Number')

        for _, tower_row in df.iterrows():
            self.add_tower()
            tower_fields = self.towers[-1]
            self.populate_tower_fields(tower_fields, tower_row)

        # Update the race name in the race_entry field
        self.race_entry.delete(0, ctk.END)
        self.race_entry.insert(0, df['Race'].iloc[0] if 'Race' in df.columns else '')

        # Update tower numbers
        for idx, tower_fields in enumerate(self.towers):
            self.update_tower_row(tower_fields, idx)



    def validate_numeric_input(self, value, field):
        try:
            if field in ['Dice', 'Sides', 'Full Splash', 'Med Splash', 'Small Splash', 'Poison', 'Gold Cost', 'Damage', 'Cooldown', 'Utility Boost']:
                int_value = int(float(value))
                if int_value < 0:
                    raise self.show_centered_message("Invalid input detected.")
            return True
        except ValueError as e:
            self.show_centered_message("Invalid input detected.")
            return False


    def apply_algorithm_changes(self):
        errors = []
        # Update calculation function
        calc_code = self.calc_function_text.get("1.0", "end")
        try:
            # Compile and replace the calculate_dps_per_gold function
            exec_globals = {}
            exec(calc_code, exec_globals)
            self.calculate_dps_per_gold = exec_globals['calculate_dps_per_gold']
            # Update self.calc_function_code with the new code
            self.calc_function_code = calc_code
        except Exception as e:
            errors.append(f"Calculation function: {e}")

        # Update preset balance ranges
        ranges_code = self.ranges_text.get("1.0", "end")
        try:
            self.preset_balance_ranges = eval(ranges_code)
        except Exception as e:
            errors.append(f"Preset balance ranges: {e}")

        # Update target type balance adjustments
        adjustments_code = self.target_type_adjustments_text.get("1.0", "end")
        try:
            self.target_type_balance_adjustments = eval(adjustments_code)
        except Exception as e:
            errors.append(f"Target type adjustments: {e}")

        if errors:
            messagebox.showerror("Error", "\n".join(errors))
        else:
            messagebox.showinfo("Success", "All changes saved successfully.")
            # Recalculate with the new algorithm
            self.calculate_all()

    def save_algorithm_to_file(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        if not file_path:
            return

        calc_code = self.calc_function_text.get("1.0", "end")
        ranges_code = self.ranges_text.get("1.0", "end")
        adjustments_code = self.target_type_adjustments_text.get("1.0", "end")

        with open(file_path, 'w') as file:
            file.write("# Calculation Function Code\n")
            file.write(calc_code.strip())
            file.write("\n\n# Preset Balance Ranges\n")
            file.write(ranges_code.strip())
            file.write("\n\n# Target Type Balance Adjustments\n")
            file.write(adjustments_code.strip())

        messagebox.showinfo("Saved", "Algorithm and adjustments saved successfully.")

    def load_algorithm(self):
        file_path = filedialog.askopenfilename(
            defaultextension=".txt",
            filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")]
        )
        if not file_path:
            return

        with open(file_path, 'r') as file:
            content = file.read()

        try:
            # Split the content based on headers
            sections = content.split('\n\n')
            calc_code = ''
            ranges_code = ''
            adjustments_code = ''
            current_section = ''
            for section in sections:
                if '# Calculation Function Code' in section:
                    current_section = 'calc_code'
                    calc_code = section.replace('# Calculation Function Code', '').strip()
                elif '# Preset Balance Ranges' in section:
                    current_section = 'ranges_code'
                    ranges_code = section.replace('# Preset Balance Ranges', '').strip()
                elif '# Target Type Balance Adjustments' in section:
                    current_section = 'adjustments_code'
                    adjustments_code = section.replace('# Target Type Balance Adjustments', '').strip()
                else:
                    if current_section == 'calc_code':
                        calc_code += '\n\n' + section.strip()
                    elif current_section == 'ranges_code':
                        ranges_code += '\n\n' + section.strip()
                    elif current_section == 'adjustments_code':
                        adjustments_code += '\n\n' + section.strip()

            # Update the text widgets
            self.calc_function_text.delete("1.0", "end")
            self.calc_function_text.insert("end", calc_code)

            self.ranges_text.delete("1.0", "end")
            self.ranges_text.insert("end", ranges_code)

            self.target_type_adjustments_text.delete("1.0", "end")
            self.target_type_adjustments_text.insert("end", adjustments_code)

            messagebox.showinfo("Loaded", "Algorithm and adjustments loaded successfully.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load algorithm:\n{e}")

    def view_dynamic_algorithm(self):
        if self.window_tracker['dynamic_algorithm'] is not None:
            try:
                self.window_tracker['dynamic_algorithm'].focus()  # Bring the window to focus if already open
            except ctk.TclError:
                # If the window is destroyed, reset the tracker
                self.window_tracker['dynamic_algorithm'] = None
        else:
            # Open a new window for viewing the dynamic algorithm
            dynamic_editor = ctk.CTkToplevel(self.root)
            self.window_tracker['dynamic_algorithm'] = dynamic_editor  # Track the window
            dynamic_editor.title("View Dynamic Algorithm")
            dynamic_editor.geometry("1100x700")

            # Bind the destroy event to reset the tracker when the window is closed
            dynamic_editor.protocol("WM_DELETE_WINDOW", lambda: self.close_window('dynamic_algorithm', dynamic_editor))
            dynamic_editor.bind("<Escape>", lambda event: self.close_window('dynamic_algorithm', dynamic_editor))

            dynamic_editor.grid_rowconfigure(1, weight=1)
            dynamic_editor.grid_columnconfigure(0, weight=1)

            ctk.CTkLabel(dynamic_editor, text="Dynamic Balance Range Calculation Code:").grid(
                row=0, column=0, sticky='nw', padx=10, pady=5
            )
            self.dynamic_calc_text = ctk.CTkTextbox(dynamic_editor, height=25, width=70)
            self.dynamic_calc_text.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")

            # Load the current dynamic calculation code
            dynamic_code = '''
### Dynamic Balance Range Calculation
# Outlier Removal: Uses IQR to exclude extreme outliers.
# Mean and Std Dev: Calculates mean and standard deviation for DPS per Gold.
# Scaling Factor: Applies a scaling factor inversely proportional to the tower number.

def calculate_dynamic_balance(df):
    balance_ranges = {}
    grouped = df.groupby(['Tower Number', 'Target Type'])
    for (tower_num, target_type), group in grouped:
        Q1 = group['DPS per Gold'].quantile(0.25)
        Q3 = group['DPS per Gold'].quantile(0.75)
        IQR = Q3 - Q1
        filtered = group[(group['DPS per Gold'] >= Q1 - 1.5 * IQR) & (group['DPS per Gold'] <= Q3 + 1.5 * IQR)]
        if filtered.empty:
            filtered = group
        mean = filtered['DPS per Gold'].mean()
        std = filtered['DPS per Gold'].std(ddof=0)
        if std == 0:
            std = mean * 0.1
        low = mean - std
        high = mean + std
        scaling_factor = 1 / (tower_num ** 0.05)
        low *= scaling_factor
        high *= scaling_factor
        balance_ranges[(tower_num, target_type)] = (low, high)
    return balance_ranges
            '''

            self.dynamic_calc_text.insert("end", dynamic_code)
            self.dynamic_calc_text.configure(state="disabled")  # Make the text read-only

        # Comments explaining each part
            comments_text = '''
# Explanation of Key Components:
# 1. Outlier Removal: This section uses IQR (Interquartile Range) to exclude extreme outliers from the DPS per Gold calculation.
#    You can modify the IQR multiplier (currently 1.5) to adjust how strict the outlier removal process is.
# 2. Mean and Standard Deviation: These are used to calculate the average DPS per Gold and its acceptable range.
# 3. Scaling Factor: As tower numbers increase, this factor slightly widens the acceptable range of balance for more expensive or powerful towers.
#    Adjusting the exponent (currently 0.05) will impact how much flexibility is allowed for higher-tier towers.
            '''
            ctk.CTkLabel(dynamic_editor, text=comments_text, justify='left', wraplength=580).grid(
                row=2, column=0, padx=10, pady=5
            )

        # Buttons
            button_frame = ctk.CTkFrame(dynamic_editor)
            button_frame.grid(row=3, column=0, pady=10)

            close_button = ctk.CTkButton(
                button_frame, text="Close", command=dynamic_editor.destroy
            )
            close_button.pack(side="left", padx=5)


    def update_analysis_window(self):
        # Check if 'analysis_text' widget exists and is viewable
        if hasattr(self, 'analysis_text') and self.analysis_text.winfo_exists() and self.analysis_text.winfo_viewable():
            analysis_text = self.analysis_text
            analysis_text.configure(state=tk.NORMAL)
            analysis_text.delete("1.0", "end")  # Clear existing content

            if hasattr(self, 'outlier_analysis_segments') and self.outlier_analysis_segments:
                for item in self.outlier_analysis_segments:
                    if isinstance(item, list):
                        # item is a list of segments
                        for text, color, *bold in item:
                            tag = color + ("_bold" if bold and bold[0] else "")
                            if tag not in analysis_text.tag_names():
                                font_style = ("Consolas", 12, "bold") if bold and bold[0] else ("Consolas", 12)
                                analysis_text.tag_configure(tag, foreground=color, font=font_style)
                            analysis_text.insert("end", text, tag)
                    elif isinstance(item, tuple) and len(item) >= 2:
                        # item is a single segment
                        text, color, *bold = item
                        tag = color + ("_bold" if bold and bold[0] else "")
                        if tag not in analysis_text.tag_names():
                            font_style = ("Consolas", 12, "bold") if bold and bold[0] else ("Consolas", 12)
                            analysis_text.tag_configure(tag, foreground=color, font=font_style)
                        analysis_text.insert("end", text, tag)
                    else:
                        # Unexpected item format
                        continue
            else:
                # Display message when there's no data
                analysis_text.insert("end", "Import data or add races to view outlier analysis and race difficulty levels.\n", "white")
                analysis_text.tag_configure("white", foreground="white", font=("Consolas", 12))

            analysis_text.configure(state=tk.DISABLED)
        else:
            print("Analysis window is not initialized or visible, skipping update.")







    def perform_comparison_analysis(self):
        analysis = ""
        outliers = {'low': pd.DataFrame(), 'high': pd.DataFrame()}
        if self.imported_df.empty:
            return "No data available for comparison analysis.", outliers

        all_tower_numbers = sorted(self.imported_df['Tower Number'].unique())
        for tower_num in all_tower_numbers:
            towers = self.imported_df[self.imported_df['Tower Number'] == tower_num]
            target_types = towers['Target Type'].unique()
            for target_type in target_types:
                towers_by_type = towers[towers['Target Type'] == target_type]
                dps_values = []
                for _, tower_row in towers_by_type.iterrows():
                    try:
                        base_damage = float(tower_row.get('Damage', 0) or 0)
                        dice = int(float(tower_row.get('Dice', 0) or 0))
                        sides = int(float(tower_row.get('Sides', 0) or 0))
                        cooldown = float(tower_row.get('Cooldown', 1) or 1)
                        if cooldown == 0:
                            cooldown = 1
                        range_val = int(float(tower_row.get('Range', 300) or 300))
                        full_splash = int(float(tower_row.get('Full Splash', 0) or 0))
                        medium_splash = int(float(tower_row.get('Med Splash', 0) or 0))
                        small_splash = int(float(tower_row.get('Small Splash', 0) or 0))
                        gold_cost = int(float(tower_row.get('Gold Cost', 1) or 1))
                        if gold_cost == 0:
                            gold_cost = 1
                        spell_dps = float(tower_row.get('Spell DPS', 0) or 0)
                        spell_dps_cooldown = float(tower_row.get('Spell DPS CD', 1) or 1)
                        if spell_dps_cooldown == 0:
                            spell_dps_cooldown = 1
                        poison = int(tower_row.get('Poison', 0))
                        slow_percentage = float(tower_row.get('Slow %', 0) or 0)
                        utility_boost = float(tower_row.get('Utility Boost', 1.0) or 1.0)
                        if utility_boost == 0:
                            utility_boost = 1.0
                        race = tower_row.get('Race', '')
                        name = tower_row.get('Name', '')

                        total_dps, dps_per_gold = self.calculate_dps_per_gold(
                            base_damage, dice, sides, cooldown, range_val, full_splash,
                            medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                            spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                            utility_boost=utility_boost, slow_percentage=slow_percentage,
                            target_type=target_type, include_splash=True)

                        dps_values.append({
                            'Race': race,
                            'Name': name,
                            'DPS per Gold': dps_per_gold,
                            'Total DPS': total_dps,
                            'Gold Cost': gold_cost,
                            'Base Damage': base_damage,
                            'Cooldown': cooldown,
                            'Range': range_val,
                            'Utility Boost': utility_boost,
                            'Slow %': slow_percentage,
                            'Tower Number': tower_num
                        })
                    except ValueError:
                        continue

            if not dps_values:
                continue

            # Convert to DataFrame
            df_tower = pd.DataFrame(dps_values)

            # Identify weakest and strongest
            weakest = df_tower.loc[df_tower['DPS per Gold'].idxmin()]
            strongest = df_tower.loc[df_tower['DPS per Gold'].idxmax()]

            # Analyze contributing factors
            factors = []
            if strongest['Base Damage'] > weakest['Base Damage']:
                factors.append("Base Damage")
            if strongest['Cooldown'] < weakest['Cooldown']:
                factors.append("Cooldown")
            if strongest['Range'] > weakest['Range']:
                factors.append("Range")
            if strongest['Utility Boost'] > weakest['Slow %']:
                factors.append("Slow %")
            if not factors:
                factors.append("Unknown")

            factor = ", ".join(factors)

            # Recommendation
            recommended_change = f"Consider adjusting {factor} for balancing."

            # Add to analysis
            separator = '─' * 50
            analysis += f"{separator}\n"
            analysis += f"**Tower {tower_num}** - **Target Type: {target_type}**\n"
            analysis += f"Weakest: {weakest['Race']} - {weakest['Name']} (DPS/Gold: {self.format_number(weakest['DPS per Gold'])})\n"
            analysis += f"Strongest: {strongest['Race']} - {strongest['Name']} (DPS/Gold: {self.format_number(strongest['DPS per Gold'])})\n"
            analysis += f"Main Contributing Factor(s): {factor}\n"
            analysis += f"Recommendation: {recommended_change}\n\n"

            # Identify Outliers
            if self.dynamic_comparison_var.get() and self.ignore_outliers_var.get():
                Q1 = df_tower['DPS per Gold'].quantile(0.25)
                Q3 = df_tower['DPS per Gold'].quantile(0.75)
                IQR = Q3 - Q1
                low_threshold = Q1 - 1.5 * IQR
                high_threshold = Q3 + 1.5 * IQR
                outliers_low = df_tower[df_tower['DPS per Gold'] < low_threshold]
                outliers_high = df_tower[df_tower['DPS per Gold'] > high_threshold]
                outliers['low'] = pd.concat([outliers['low'], outliers_low])
                outliers['high'] = pd.concat([outliers['high'], outliers_high])

        return analysis, outliers

        

    def clear_all(self):
        """
        Clears all input fields and resets the calculation results box after user confirmation.
        """
        if messagebox.askyesno("Confirm Clear All", "Are you sure you want to clear all fields and reset the results?"):
            # Clear the calculation results text box
            self.result_text.delete("1.0", "end")

            # Clear the "Race:" text box
            self.race_entry.delete(0, "end")

            # Clear the race combobox
            self.race_combobox.set('')

            # Iterate through each tower and reset its fields
            for tower in self.towers:
                self.clear_tower_fields(tower)

    def clear_all_skip_message(self):
            # Clear the calculation results text box
            self.result_text.delete("1.0", "end")

            # Clear the "Race:" text box
            self.race_entry.delete(0, "end")

            # Clear the race combobox
            self.race_combobox.set('')

            # Iterate through each tower and reset its fields
            for tower in self.towers:
                self.clear_tower_fields(tower)

if __name__ == "__main__":
    ctk.set_appearance_mode("Dark")  # Modes: "System" (default), "Dark", "Light"
    ctk.set_default_color_theme("dark-blue")  # Themes: "blue" (default), "green", "dark-blue"

    root = ctk.CTk()
    app = TowerApp(root)
    root.mainloop()