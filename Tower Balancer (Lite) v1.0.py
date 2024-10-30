import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import pandas as pd
import numpy as np
import math
from scipy import stats  # Added for Z-Score and Percent Rank calculations

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
        self.waittime = 500     # milliseconds
        self.wraplength = 250   # pixels
        self.widget = widget
        self.text = text
        self.widget.bind("<Enter>", self.enter)
        self.widget.bind("<Leave>", self.leave)
        self.widget.bind("<ButtonPress>", self.leave)
        self.id = None
        self.tw = None

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
        self.tw = tk.Toplevel(self.widget)
        self.tw.wm_overrideredirect(True)  # removes the window decorations
        self.tw.wm_geometry("+%d+%d" % (x, y))
        self.tw.wm_attributes("-topmost", True)  # Ensures tooltip is on top
        label = tk.Label(self.tw, text=self.text, justify='left',
                         background='lightyellow', relief='solid', borderwidth=1,
                         wraplength = self.wraplength)
        label.pack(ipadx=1)
    def hidetip(self):
        tw = self.tw
        self.tw= None
        if tw:
            tw.destroy()

class TowerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Warcraft 3 Tower Balancer by Aphotica (Discord: https://discord.gg/Qsg6UDn)")
        self.root.geometry("1455x700")  # Expanded width by 100 pixels
        self.root.resizable(False, True)

        self.window_tracker = {
            'algorithm_editor': None,
            'dynamic_algorithm': None,
            'analysis': None,
            'help': None
        }

        self.focused_row = None

        # Set the style
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TFrame', background='white')
        style.configure('TLabel', background='white', foreground='black')
        style.configure('White.TLabel', background='white', foreground='black')
        style.configure('TButton', background='lightgray', foreground='black')
        style.configure('TEntry', fieldbackground='white', foreground='black')
        style.configure('White.TEntry', fieldbackground='white', foreground='black')
        style.configure('TCheckbutton', background='white', foreground='black')
        style.configure('White.TCheckbutton', background='white', foreground='black')

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
            self.root.bind(f"<Key-{i}>", self.on_numeric_key_pressed)
        self.root.bind('<Delete>', lambda event: self.calculate_all())
        self.root.bind('<BackSpace>', lambda event: self.calculate_all())

    def on_numeric_key_pressed(self, event):
        """
        This method is triggered whenever a numeric key is pressed (0-9).
        It calls the calculate_all method.
        """
        self.calculate_all()
        self.root.bind('<Return>', lambda event: self.calculate_all())


    def set_focused_row(self, row_frame):
        """
        Sets the given row_frame as the focused row and updates the background colors accordingly.
        Resets the background of the previously focused row if it's different from the current one.
        """
        if self.focused_row and self.focused_row != row_frame:
            try:
                if self.focused_row.winfo_exists():
                    self.focused_row.config(background='white')  # Reset previous row's background
            except tk.TclError:
                pass  # The focused row no longer exists

        self.focused_row = row_frame
        try:
            if self.focused_row.winfo_exists():
                self.focused_row.config(background='#7abdf5')  # Set current row's background to purple
        except tk.TclError:
            self.focused_row = None  # Reset if the frame no longer exists


    def setup_ui(self):
        self.main_frame = ttk.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True)

        # Configure grid layout for main_frame
        self.main_frame.columnconfigure(0, weight=1)
        self.main_frame.rowconfigure(1, weight=1)
        self.main_frame.rowconfigure(2, weight=0)  # For bottom buttons
        self.main_frame.rowconfigure(3, weight=0)  # For result text box

        # Header Frame
        header_frame = ttk.Frame(self.main_frame)
        header_frame.grid(row=0, column=0, sticky='ew', padx=10, pady=5)
        header_frame.columnconfigure(1, weight=1)

        # Add a "Help" button to the header frame, to the right of "Analysis"
        self.help_button = ttk.Button(header_frame, text="Help", command=self.open_help_window)
        self.help_button.pack(side=tk.RIGHT, padx=5)

        # Analysis Button
        self.analysis_button = ttk.Button(header_frame, text="Analysis", command=self.show_comparison)
        self.analysis_button.pack(side=tk.RIGHT, padx=5)

        # Clear All Button
        self.clear_all_button = ttk.Button(header_frame, text="Clear All", command=self.clear_all)
        self.clear_all_button.pack(side=tk.RIGHT, padx=5)

        tk.Label(header_frame, text="Race:").pack(side=tk.LEFT)
        self.race_entry = ttk.Entry(header_frame, width=20)
        self.race_entry.pack(side=tk.LEFT)

        # Export and Import buttons in a frame
        export_import_frame = ttk.Frame(header_frame)
        export_import_frame.pack(side=tk.LEFT, padx=10)

        self.export_button = ttk.Button(export_import_frame, text="Export", command=self.export_data)
        self.export_button.pack(side=tk.LEFT, padx=5)

        self.import_button = ttk.Button(export_import_frame, text="Import", command=self.import_data)
        self.import_button.pack(side=tk.LEFT, padx=5)

        # Add padding between Export/Import and Algorithm button
        spacer = ttk.Frame(header_frame, width=50)
        spacer.pack(side=tk.LEFT)

        # Algorithm button
        self.algorithm_button = ttk.Button(header_frame, text="Algorithm", command=self.open_algorithm_editor)
        self.algorithm_button.pack(side=tk.LEFT, padx=10)

        # Dynamic Comparison Checkbox
        self.dynamic_comparison_var = tk.BooleanVar(value=True)
        self.dynamic_comparison_chk = ttk.Checkbutton(header_frame, text="Dynamic Comparison",
                                                      variable=self.dynamic_comparison_var, command=self.calculate_all)
        self.dynamic_comparison_chk.pack(side=tk.LEFT, padx=5)

        # Ignore Outliers Checkbox
        self.ignore_outliers_var = tk.BooleanVar(value=True)
        self.ignore_outliers_chk = ttk.Checkbutton(header_frame, text="Ignore Outliers",
                                                   variable=self.ignore_outliers_var, command=self.calculate_all)
        self.ignore_outliers_chk.pack(side=tk.LEFT, padx=5)

        # Race selection Combobox
        tk.Label(header_frame, text="Select Race:").pack(side=tk.LEFT)
        self.race_combobox = ttk.Combobox(header_frame, state="readonly")
        self.race_combobox.pack(side=tk.LEFT)
        self.race_combobox.bind('<<ComboboxSelected>>', self.on_race_selected)

        # Towers Frame Container
        towers_frame_container = ttk.Frame(self.main_frame)
        towers_frame_container.grid(row=1, column=0, sticky='nsew')
        towers_frame_container.columnconfigure(0, weight=1)
        towers_frame_container.rowconfigure(1, weight=1)

        # Towers Header Frame
        towers_header_frame = ttk.Frame(towers_frame_container)
        towers_header_frame.grid(row=0, column=0, sticky='ew')

        # Towers Frame with Scrollbar
        self.towers_canvas = tk.Canvas(towers_frame_container, highlightthickness=0, background='white')
        self.towers_canvas.grid(row=1, column=0, sticky='nsew')

        towers_scrollbar = ttk.Scrollbar(towers_frame_container, orient=tk.VERTICAL, command=self.towers_canvas.yview)
        towers_scrollbar.grid(row=1, column=1, sticky='ns')

        self.towers_canvas.configure(yscrollcommand=towers_scrollbar.set)

        self.towers_frame = ttk.Frame(self.towers_canvas)
        self.towers_canvas.create_window((0, 0), window=self.towers_frame, anchor='nw')

        # Update scrollregion when towers_frame is resized
        self.towers_frame.bind("<Configure>", self.on_towers_frame_configure)

        # Bind scroll wheel only to the towers canvas
        self.towers_canvas.bind("<Enter>", lambda e: self.towers_canvas.bind_all("<MouseWheel>", self._on_mousewheel))
        self.towers_canvas.bind("<Leave>", lambda e: self.towers_canvas.unbind_all("<MouseWheel>"))

        # Create headers in towers_header_frame
        self.create_headers(towers_header_frame)

        # Create initial towers
        for _ in range(11):
            self.add_tower()

        # Buttons at the bottom
        bottom_button_frame = ttk.Frame(self.main_frame)
        bottom_button_frame.grid(row=2, column=0, sticky='ew', padx=10, pady=5)

        self.calculate_button = ttk.Button(bottom_button_frame, text="Calculate All", command=self.calculate_all)
        self.calculate_button.pack(side=tk.LEFT, padx=5)

        # Add more space between buttons
        spacer = ttk.Frame(bottom_button_frame, width=50)
        spacer.pack(side=tk.LEFT)

        self.add_tower_button = ttk.Button(bottom_button_frame, text="Add Tower", command=self.add_tower)
        self.add_tower_button.pack(side=tk.LEFT, padx=5)

        self.delete_tower_button = ttk.Button(bottom_button_frame, text="Delete Tower", command=self.delete_last_tower)
        self.delete_tower_button.pack(side=tk.LEFT, padx=5)

        # Result Text with Scrollbar
        result_frame = ttk.Frame(self.main_frame)
        result_frame.grid(row=3, column=0, sticky='nsew', padx=10, pady=10)
        result_frame.columnconfigure(0, weight=1)
        result_frame.rowconfigure(0, weight=1)

        self.result_text = tk.Text(result_frame, height=13)  # Increased height to accommodate 12 towers
        self.result_text.grid(row=0, column=0, sticky='nsew')

        result_scrollbar = ttk.Scrollbar(result_frame, orient=tk.VERTICAL, command=self.result_text.yview)
        self.result_text.configure(yscrollcommand=result_scrollbar.set)
        result_scrollbar.grid(row=0, column=1, sticky='ns')

        # Add tag configurations for coloring
        self.result_text.tag_configure("green", foreground="green")
        self.result_text.tag_configure("red", foreground="red")
        self.result_text.tag_configure("blue", foreground="blue")  # For tower numbers
        self.result_text.tag_configure("purple", foreground="purple")  # For outliers

        # Add tag configuration for headers
        self.result_text.tag_configure("header", foreground="blue", font=("Courier", 10, "bold"))

        # Add tag configuration for outlier headers
        self.result_text.tag_configure("outlier_header", foreground="blue", font=("TkDefaultFont", 10, "bold"))

    def create_headers(self, parent_frame):
        self.headers = ['No.', 'Name', 'Gold Cost', 'Damage', 'Dice','Sides', 'Cooldown', 'Range',
                        'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                        'Slow %', 'Utility Boost', 'Poison',''] 

        tooltips = {
            'No.': 'Tower number',
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
            'Poison': 'Applies poison effect that slows and damages over time',
        }

        # Define column widths
        self.column_widths = [5, 20, 10, 10, 8, 8, 12, 10, 12, 12, 12, 12, 14, 10, 14, 8, 20]

        # Configure columns in parent_frame
        for idx in range(len(self.headers)):
            parent_frame.columnconfigure(idx, weight=1)

        # Create headers
        for idx, header in enumerate(self.headers):
            lbl = ttk.Label(parent_frame, text=header, anchor='center', width=self.column_widths[idx], style='White.TLabel')
            lbl.grid(row=0, column=idx, padx=5, pady=2, sticky='nsew')
            lbl.configure(font=('TkDefaultFont', 10, 'bold'))
            Tooltip(lbl, text=tooltips.get(header, ''))

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

    def check_for_changes(self, tower_index, field):
        """
        Check if the current value of the tower field has changed more than 0.1% from its original value.
        If yes, change the tower number to red and bold. If within 0.1%, revert it to normal.
        """
        tower_fields = self.towers[tower_index]

        # Get the current value from the respective field (handle checkbutton separately)
        if field == 'Poison':
            current_value = tower_fields[field].get()
        else:
            current_value = tower_fields[field].get()

        # Get the original value stored in 'original_values'
        original_value = tower_fields['original_values'][field]

        # Ignore empty values (we don't track differences for blank fields)
        if not current_value or not original_value:
            return

        try:
            # Convert current and original values to floats for comparison (skip Poison as it's boolean)
            if field != 'Poison':
                current_value = float(current_value)
                original_value = float(original_value)
                if original_value != 0:
                    # Calculate the percentage difference
                    difference = abs(current_value - original_value) / original_value * 100
                else:
                    difference = 100  # If the original value is 0, consider any change a 100% difference
            else:
                difference = abs(current_value - original_value) * 100  # For Poison (boolean comparison)

            # If the difference exceeds 0.1%, set tower number label to red and bold
            if difference > 0.1:
                tower_fields['No.'].config(foreground="red", font=("TkDefaultFont", 10, "bold"))
            else:
                # If within the 0.1% threshold, revert to black and normal font
                tower_fields['No.'].config(foreground="black", font=("TkDefaultFont", 10, "normal"))

        except ValueError:
            pass  # In case the values can't be converted to float, skip the comparison

    def open_help_window(self):
        if self.window_tracker['help'] is not None:
            try:
                self.window_tracker['help'].focus()  # Bring the window to focus if already open
            except tk.TclError:
                # If the window was closed unexpectedly, reset the tracker
                self.window_tracker['help'] = None
        else:
            # Create a new Help window
            help_win = tk.Toplevel(self.root)
            self.window_tracker['help'] = help_win  # Track the window
            help_win.title("Help")
            help_win.geometry("800x600")
            help_win.resizable(True, True)
        
            # Bind the destroy event to reset the tracker when the window is closed
            help_win.protocol("WM_DELETE_WINDOW", lambda: self.close_window('help', help_win))
            help_win.bind("<Escape>", lambda event: self.close_window('help', help_win))
        
            # Create a Text widget with scrollbars
            help_text_frame = ttk.Frame(help_win)
            help_text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
            help_text = tk.Text(help_text_frame, wrap='word')
            help_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
            help_scrollbar = ttk.Scrollbar(help_text_frame, orient=tk.VERTICAL, command=help_text.yview)
            help_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            help_text.configure(yscrollcommand=help_scrollbar.set)
        
            # Insert help content
            help_content = """
            Warcraft 3 Tower Balancer - Help Guide
            ===========================================

            **Introduction**
            ----------------
            The Tower Balancer is a tool designed to assist WC3 tower defense developers in evaluating and adjusting tower statistics for games like Wintermaul Wars (WMW). By analyzing various tower attributes and their impact on gameplay, this tool ensures that towers are balanced, providing a fair and competitive environment.
            
            This tool was created to be used in Wintermaul Wars X16, where there are over 40 races and 500 towers, but may be used for any TD in WC3.

            The dynamic algorithm improves accuracy with an increasing amount of data. It is recommended to have at least 10 races/data sets available. Otherwise, disable this in your calculation and use the standard algorithm with preset balance ranges located in the algorithm editor (adjust the ranges to your needs)
            
            **Main Features**
            -----------------
            1. **Data Input:**
            - **Name:** Assign a unique name to each tower.
            - **Gold Cost:** The cost to build the tower in the game.
            - **Damage:** Base damage per hit.
            - **Dice & Sides:** Number of dice and sides per die for randomized damage.
            - **Cooldown:** Time (in seconds) between each attack.
            - **Range:** Attack range of the tower.
            - **Splash Damage:** Probabilities for full, medium, and small splash damage.
            - **Spell DPS & Cooldown:** Custom spell damage per second and its cooldown.
            - **Poison:** Applies a poison effect that slows and damages over time.
            - **Slow %:** Percentage reduction in enemy movement speed.
            - **Utility Boost:** Damage multiplier for utility effects.
            - **Target Type:** Determines if a tower has specific splash damage criteria (All, Ground Splash, Air Splash).

            2. **Dynamic Balance Calculation:**
            - Computes the mean and standard deviation of DPS per Gold across all towers.
            - Defines a balanced range as mean ± one standard deviation.
            - Applies a scaling factor inversely proportional to the tower number to account for progression.

            3. **Outlier Removal:**
            - Utilizes the Interquartile Range (IQR) method to exclude extreme outliers.
            - Adjusts calculations based on whether outliers are ignored.

            4. **Statistical Analysis:**
            - Calculates Z-Scores and Percentile Ranks for each tower's DPS per Gold.
            - Determines balance status: Balanced, Underpowered, or Overpowered.
            - Balance status returns "Balanced" if towers are within dynamic range, have a Z-score between -1 and 1, and a percentile rank between 40-60%
            - Separates Ground Splash vs Air Splash only targets and returns an appropriate balance range where these towers have an advantage with splash damage and a disadvantage of single-target DPS.

            5. **Export & Import:**
            - Save tower configurations to an Excel file.
            - Import existing tower data for analysis and adjustments.

            6. **Algorithm Editor:**
            - Modify the DPS calculation algorithm.
            - Adjust preset balance ranges and target type balance adjustments.

            **Understanding the Algorithm**
            --------------------------------
            The core of the Tower Balancer lies in its algorithm, which calculates each tower's effectiveness relative to its gold cost.

            DPS/Gold is multiplied by 100 for better analysis as this code was originally fine-tuned specifically for the scaling in Wintermaul Wars. This factor has no effect on the accuracy of the results.

            1. **DPS Calculation:**
            - **Average Damage:** Calculated as `base_damage + (dice * (sides_per_die + 1) / 2)`.
            - **Hits Per Second:** `1 / cooldown`.
            - **Base DPS:** `average_damage * hits_per_second`.
            - **Range Adjustment:** Applies a polynomial modifier based on the tower's range.
            - **Splash DPS:** Calculates additional DPS from splash damage probabilities.
            - **Spell DPS:** Incorporates custom spell effects and their cooldowns.
            - **Poison & Slow Effects:** Adds DPS contributions from poison and slow effects.
            - **Utility Boost:** Applies a multiplier to the total DPS.

            2. **Balance Range Determination:**
            - **Mean & Standard Deviation:** Determines the average DPS per Gold and its variability.
            - **Scaling Factor:** Adjusts the balance range based on the tower number, allowing higher-numbered towers a slightly wider range.
            - **Final Balance Range:** `mean - std_dev` to `mean + std_dev`, scaled accordingly.

            3. **Balance Status:**
            - **Balanced:** Tower's DPS per Gold is within the balance range, with acceptable Z-Score and Percentile Rank.
            - **Underpowered:** Below the lower bound or percentile.
            - **Overpowered:** Above the upper bound or percentile.

            **Using the Algorithm Editor**
            --------------------------------
            - **Accessing the Editor:**
            - Click the "Algorithm" button to open the Algorithm Editor.
            - Modify the DPS calculation code, preset balance ranges, and target type balance adjustments as needed.
            - Save and apply changes to update the balance calculations in real-time.

            - **Safety Precautions:**
            - Ensure that any modifications to the algorithm maintain the integrity of the calculations.
            - Invalid code or incorrect range definitions may lead to errors or inaccurate balance assessments.

            **Best Practices**
            -------------------
            - **Regular Testing:** Continuously test tower configurations in-game to validate the balance assessments provided by the tool.
            - **Iterative Adjustments:** Use the tool to make small, incremental changes rather than large overhauls to maintain game balance.
            - **Community Feedback:** Incorporate feedback from players to identify balance issues that may not be evident through statistical analysis alone.

            **Contact**
            ---------------
                       For further assistance or inquiries, please refer to the official documentation or contact Aphotica on discord.

            """
            help_text.insert(tk.END, help_content)
            help_text.configure(state=tk.DISABLED)  # Make the text read-only


    def add_tower(self):
        row = len(self.towers)  # No need to offset by 1
        tower_fields = {}

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
            'Poison': 0
        }

        # Create a Frame for the row
        row_frame = tk.Frame(self.towers_frame, background='white')
        row_frame.grid(row=row, column=0, columnspan=len(self.headers), sticky='nsew')
        tower_fields['row_frame'] = row_frame

        # Configure columns in row_frame
        for idx in range(len(self.headers)):
            row_frame.columnconfigure(idx, weight=1)

        # Bind events to highlight the row
        def on_enter_row(event, frame=row_frame):
            if frame != self.focused_row:
                frame.config(background='#D0E4F5')  # Light blue highlight

        def on_leave_row(event, frame=row_frame):
            if frame != self.focused_row:
                frame.config(background='white')  # Remove highlight

        def on_focus_row(event, frame=row_frame):
            self.set_focused_row(frame)  # Set this row as focused

        def on_focus_out_row(event, frame=row_frame):
            # Check if any widget in the row still has focus
            has_focus = any(widget.focus_displayof() for widget in frame.winfo_children())
            if not has_focus and self.focused_row == frame:
                frame.config(background='white')  # Reset background
                self.focused_row = None  # Unset the focused row

        # Tower number label
        tower_number_label = ttk.Label(row_frame, text=str(row+1), anchor='center', width=self.column_widths[0], style='White.TLabel', background='white')
        tower_number_label.grid(row=0, column=0, padx=2, pady=2, sticky='nsew')
        tower_fields['No.'] = tower_number_label

        # Create entries for each field
        fields = ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                  'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                  'Slow %', 'Utility Boost']

        for col, field in enumerate(fields, start=1):
            entry = ttk.Entry(row_frame, width=self.column_widths[col], justify='center', style='White.TEntry')
            entry.grid(row=0, column=col, padx=5, pady=2, sticky='nsew')
            tower_fields[field] = entry

            # Store the initial value in 'original_values'
            tower_fields['original_values'][field] = entry.get()

            # Bind mousewheel to each widget to ensure scrolling works when mouse is over them
            entry.bind("<MouseWheel>", self._on_mousewheel)
            # Bind events for highlighting
            entry.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
            entry.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
            entry.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
            entry.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

            # Bind event listeners for change detection
            entry.bind("<KeyRelease>", lambda e, field=field, tower_index=row: self.check_for_changes(tower_index, field))

            # Bind arrow key navigation
            entry.bind("<Up>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'up'))
            entry.bind("<Down>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'down'))
            entry.bind("<Left>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'left', e))
            entry.bind("<Right>", lambda e, current_row=row, col=col-1: self.navigate_entry(current_row, col, 'right', e))

        # Poison Checkbutton
        poison_var = tk.IntVar()
        poison_chk = tk.Checkbutton(row_frame, variable=poison_var, background='white', command=self.calculate_all)
        poison_chk.grid(row=0, column=len(fields)+1, padx=2, sticky='')
        tower_fields['Poison'] = poison_var
        tower_fields['Poison_chk'] = poison_chk
        tower_fields['original_values']['Poison'] = poison_var.get()

        Tooltip(poison_chk, text='Applies poison effect that slows and damages over time')

        # Center the checkbox
        poison_chk.grid_configure(padx=2)
        # Bind mousewheel to checkbutton
        poison_chk.bind("<MouseWheel>", self._on_mousewheel)
        # Bind events for highlighting
        poison_chk.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
        poison_chk.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
        poison_chk.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
        poison_chk.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

        # Bind event listener for the Poison checkbox change detection
        poison_chk.bind("<ButtonRelease>", lambda e, field='Poison', tower_index=row: self.check_for_changes(tower_index, field))

        # Target Type Combobox
        target_type_var = tk.StringVar()
        target_type_combobox = ttk.Combobox(row_frame, textvariable=target_type_var, state='readonly', width=self.column_widths[len(fields)+1])
        target_type_combobox['values'] = ('All', 'Ground Splash', 'Air Splash')
        target_type_combobox.current(0)  # default to 'All'
        target_type_combobox.grid(row=0, column=len(fields)+2, padx=2, sticky='nsew')
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
        reset_button = ttk.Button(row_frame, text="Reset", command=lambda idx=len(self.towers): self.reset_tower(idx))
        reset_button.grid(row=0, column=len(fields)+6, padx=2, sticky='nsew')
        tower_fields['reset_button'] = reset_button
        # Bind mousewheel to reset button
        reset_button.bind("<MouseWheel>", self._on_mousewheel)
        # Bind events for highlighting
        reset_button.bind("<Enter>", lambda e, frame=row_frame: on_enter_row(e, frame))
        reset_button.bind("<Leave>", lambda e, frame=row_frame: on_leave_row(e, frame))
        reset_button.bind("<FocusIn>", lambda e, frame=row_frame: on_focus_row(e, frame))
        reset_button.bind("<FocusOut>", lambda e, frame=row_frame: on_focus_out_row(e, frame))

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
        tower_number_label.config(text=str(row+1))
        # Re-grid the row_frame
        tower_fields['row_frame'].grid(row=row, column=0, columnspan=len(self.headers), sticky='nsew')
        # Update reset button command
        reset_button = tower_fields['reset_button']
        reset_button.configure(command=lambda idx=row: self.reset_tower(idx))

    def reset_tower(self, index):
        if not self.original_imported_df.empty:
            # Get the race and tower number
            race_name = self.race_entry.get()
            tower_number = index + 1
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
            self.calculate_all()
        else:
            # Clear the fields if no data is imported
            self.clear_tower_fields(self.towers[index])


    def populate_tower_fields(self, tower_fields, tower_row):
        # Clear existing entries
        self.clear_tower_fields(tower_fields)

        # Fields that should be rounded to integers
        integer_fields = ['Damage', 'Full Splash', 'Med Splash', 'Small Splash']

        # Populate fields
        for field in ['Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
                    'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
                    'Slow %', 'Utility Boost']:
            value = tower_row.get(field, '')
            if pd.isna(value):
                value = ''
            else:
                if value == 0:
                    value = ''
                else:
                    # Round to integer for the specified fields
                    if field in integer_fields:
                        value = str(int(round(value)))  # Convert to integer and back to string
                    else:
                        value = str(value)
            tower_fields[field].insert(0, value)

        # Set checkbuttons
        poison_value = tower_row.get('Poison', 0)
        if pd.isna(poison_value):
            poison_value = 0
        tower_fields['Poison'].set(int(poison_value))

        # Set Target Type
        target_type_value = tower_row.get('Target Type', 'All')
        if pd.isna(target_type_value) or target_type_value not in ('All', 'Ground Splash', 'Air Splash'):
            target_type_value = 'All'
        tower_fields['Target Type'].set(target_type_value)



    def clear_tower_fields(self, tower_fields):
        fields_to_clear = [
            'Name', 'Gold Cost', 'Damage', 'Dice', 'Sides', 'Cooldown', 'Range',
            'Full Splash', 'Med Splash', 'Small Splash', 'Spell DPS', 'Spell DPS CD',
            'Slow %', 'Utility Boost'
        ]
        for field in fields_to_clear:
            entry_widget = tower_fields.get(field)
            if entry_widget:
                entry_widget.delete(0, tk.END)

        # Uncheck the Poison checkbox
        poison_var = tower_fields.get('Poison')
        if poison_var:
            poison_var.set(0)

        # Reset Target Type to default ('All')
        target_type_var = tower_fields.get('Target Type')
        if target_type_var:
            target_type_var.set('All')

        # Clear Z-Score and Percent Rank
        z_score_var = tower_fields.get('Z-Score')
        if z_score_var:
            z_score_var.set('')
        percent_rank_var = tower_fields.get('Percent Rank')
        if percent_rank_var:
            percent_rank_var.set('')
        balance_status_var = tower_fields.get('Balance Status')
        if balance_status_var:
            balance_status_var.set('')

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
            if event and entry.index(tk.INSERT) == 0:
                if current_col > 0:
                    target_entry = self.towers[current_row][self.get_field_by_col(current_col - 1)]
                    target_entry.focus_set()
                    target_entry.icursor('end')
        elif direction == 'right':
            entry = self.towers[current_row][self.get_field_by_col(current_col)]
            if event and entry.index(tk.INSERT) == len(entry.get()):
                if current_col < len(self.headers) - 4:  # Exclude Poison, Target Type, Z-Score, Percent Rank, and Reset columns
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
        elif col == len(fields) + 2:  # Z-Score
            return 'Z-Score'
        elif col == len(fields) + 3:  # Percent Rank
            return 'Percent Rank'
        elif col == len(fields) + 4:  # Balance Status
            return 'Balance Status'
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

    def calculate_all(self):
        self.result_text.delete(1.0, tk.END)

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
                self.result_text.insert(tk.END, f"Tower {i+1}: Invalid input - {e}\n", "red")

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
                    poison = int(tower_row.get('Poison', 0))
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
                    base_low, base_high = self.balance_ranges.get((tower_number, 'All'), (0, 0))
                else:
                    # Use preset balance ranges
                    base_low, base_high = self.preset_balance_ranges.get(tower_number, (0, 0))

                # Get global ranges
                global_dps_per_gold_min, global_dps_per_gold_max = self.global_dps_per_gold_ranges.get((tower_number, 'All'), (0, 0))
                global_raw_dps_min, global_raw_dps_max = self.global_raw_dps_ranges.get((tower_number, 'All'), (0, 0))

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
                        'Raw DPS': total_dps_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str,
                        'Z-Score': z_score_str,          # Added
                        'Percent Rank': percent_rank_str # Added
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

                    # Prepare data for display (Ground)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Ground)",
                        'DPS per Gold': dps_per_gold_ground_str,
                        'Balance Status': balance_status_ground,
                        'Balance Range': balance_range_ground_str,
                        'Raw DPS': total_dps_ground_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str,
                        'Z-Score': z_score_ground_str,          # Added
                        'Percent Rank': percent_rank_ground_str # Added
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
                        'Raw DPS': total_dps_air_str,
                        'Target': 'Air',
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str,
                        'Z-Score': z_score_air_str,          # Added
                        'Percent Rank': percent_rank_air_str # Added
                    })

                elif target_type == 'Air Splash':
                    # Primary Variant: Air Splash with 1.5x 'All' balance range and splash damage
                    total_dps_air, dps_per_gold_air = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, full_splash,
                        medium_splash, small_splash, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type=target_type, include_splash=True)

                    # Adjust balance ranges (1.5x 'All' balance range)
                    adjusted_low_air = base_low * 1.5
                    adjusted_high_air = base_high * 1.5

                    # **Retrieve Z-Score and Percent Rank for Air Splash**
                    z_score_air_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_air_row.empty:
                        z_score_air = z_score_air_row.values[0]
                    else:
                        z_score_air = 0  # Default value if not found

                    percent_rank_air_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == target_type) &
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
                    global_dps_per_gold_str = f"{self.format_number(global_dps_per_gold_min)} - {self.format_number(global_dps_per_gold_max)}"
                    global_raw_dps_str = f"{self.format_number(global_raw_dps_min)} - {self.format_number(global_raw_dps_max)}"

                    # Retrieve Z-Score string
                    z_score_air_str = f"{round(z_score_air, 2)}"

                    # Prepare data for display (Air)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Air)",
                        'DPS per Gold': dps_per_gold_air_str,
                        'Balance Status': balance_status_air,
                        'Balance Range': balance_range_air_str,
                        'Raw DPS': total_dps_air_str,
                        'Target': target_type,
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str,
                        'Z-Score': z_score_air_str,          # Added
                        'Percent Rank': percent_rank_air_str # Added
                    })

                    # Secondary Variant: Ground with 0.5x 'All' balance range and no splash damage
                    total_dps_ground, dps_per_gold_ground = self.calculate_dps_per_gold(
                        base_damage, dice, sides, cooldown, range_val, 0, 0, 0, gold_cost, spell_dps=spell_dps,
                        spell_dps_cooldown=spell_dps_cooldown, poison=poison,
                        utility_boost=utility_boost, slow_percentage=slow_percentage,
                        target_type='Ground', include_splash=False)

                    # Adjust balance ranges (0.5x 'All' balance range)
                    adjusted_low_ground = base_low * 0.5
                    adjusted_high_ground = base_high * 0.5

                    # **Retrieve Z-Score and Percent Rank for Ground Variant**
                    z_score_ground_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Ground') &
                        (df_all_towers['Race'] == selected_race),
                        'Z-Score'
                    ]

                    if not z_score_ground_row.empty:
                        z_score_ground = z_score_ground_row.values[0]
                    else:
                        z_score_ground = 0  # Default value if not found

                    percent_rank_ground_row = df_all_towers.loc[
                        (df_all_towers['Tower Number'] == tower_number) &
                        (df_all_towers['Target Type'] == 'Ground') &
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

                    # Retrieve Z-Score string
                    z_score_ground_str = f"{round(z_score_ground, 2)}"

                    # Prepare data for display (Ground Variant)
                    race_tower_data.append({
                        'Tower Number': tower_number,
                        'Tower Name': tower_name + " (Ground)",
                        'DPS per Gold': dps_per_gold_ground_str,
                        'Balance Status': balance_status_ground,
                        'Balance Range': balance_range_ground_str,
                        'Raw DPS': total_dps_ground_str,
                        'Target': 'Ground',
                        'Global DPS per Gold': global_dps_per_gold_str,
                        'Global Raw DPS': global_raw_dps_str,
                        'Z-Score': z_score_ground_str,          # Added
                        'Percent Rank': percent_rank_ground_str # Added
                    })

                else:
                    # Handle unexpected target types
                    continue

            except ValueError as e:
                self.result_text.insert(tk.END, f"Tower {tower_number}: Invalid - {e}\n", "red")

        # Adjust format_string to reflect the new order
        format_string = "{:<6} {:<30} {:<12} {:<15} {:<15} {:<10} {:<10} {:<12} {:<15} {:<15} {:<15}\n"

        # Adjust the header to reflect the new order
        header = format_string.format(
            "Tower", "Name", "DPS/Gold", "Status", "Balance Range", "Z-Score", "Rank", "Raw DPS",
            "Target", "Global DPS/Gold", "Global Raw DPS"
        )

        # Insert the header at the beginning of the result box
        self.result_text.insert(tk.END, header, "header")
        self.result_text.insert(tk.END, "-" * 160 + "\n")

        # Display the results
        for data in race_tower_data:
            # Color-code tower numbers
            tower_num_str = f"{data['Tower Number']}"
            tower_num_formatted = tower_num_str
            result = format_string.format(
                tower_num_formatted, data['Tower Name'], data['DPS per Gold'], data['Balance Status'],
                data['Balance Range'], data['Z-Score'], data['Percent Rank'], data['Raw DPS'], 
                data['Target'], data['Global DPS per Gold'], data['Global Raw DPS']
            )

            # Determine the tag based on Balance Status
            if data['Balance Status'] == "Balanced":
                tag = "green"
            else:
                tag = "red"

            self.result_text.insert(tk.END, result, tag)

        # Append Outlier Section with Race context
        outliers_low = df_all_towers[df_all_towers['DPS per Gold'] < df_all_towers.groupby(['Tower Number', 'Target Type'])['DPS per Gold'].transform(lambda x: x.quantile(0.05))]
        outliers_high = df_all_towers[df_all_towers['DPS per Gold'] > df_all_towers.groupby(['Tower Number', 'Target Type'])['DPS per Gold'].transform(lambda x: x.quantile(0.95))]

        if not outliers_low.empty or not outliers_high.empty:
            self.result_text.insert(tk.END, "\n" + "="*160 + "\n", ())
            self.result_text.insert(tk.END, "Outlier Analysis:\n", "outlier_header")
            
            # Low-End Outliers
            if not outliers_low.empty:
                self.result_text.insert(tk.END, "\nLow-End Outliers:\n", "red")
                for _, row in outliers_low.iterrows():
                    # Retrieve balance range
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_range_str = f"{self.format_number(balance_range[0])} - {self.format_number(balance_range[1])}"
                    
                    # Create outlier string with balance range
                    # Split the string into parts for different colors
                    tower_info = f"Tower {row['Tower Number']} ({row['Race']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_info = f" (Balance Range: {balance_range_str})\n"
                    
                    # Insert tower info in blue
                    self.result_text.insert(tk.END, tower_info, "blue")
                    # Insert DPS/Gold in red
                    self.result_text.insert(tk.END, dps_gold, "red")
                    # Insert balance range in black
                    self.result_text.insert(tk.END, balance_info, "black")
            
            # High-End Outliers
            if not outliers_high.empty:
                self.result_text.insert(tk.END, "\nHigh-End Outliers:\n", "red")
                for _, row in outliers_high.iterrows():
                    # Retrieve balance range
                    balance_range = self.balance_ranges.get((row['Tower Number'], row['Target Type']), (0, 0))
                    balance_range_str = f"{self.format_number(balance_range[0])} - {self.format_number(balance_range[1])}"
                    
                    # Create outlier string with balance range
                    # Split the string into parts for different colors
                    tower_info = f"Tower {row['Tower Number']} ({row['Race']}) - "
                    dps_gold = f"DPS/Gold: {self.format_number(row['DPS per Gold'])}"
                    balance_info = f" (Balance Range: {balance_range_str})\n"
                    
                    # Insert tower info in blue
                    self.result_text.insert(tk.END, tower_info, "blue")
                    # Insert DPS/Gold in red
                    self.result_text.insert(tk.END, dps_gold, "red")
                    # Insert balance range in black
                    self.result_text.insert(tk.END, balance_info, "black")




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
        if not self.race_entry.get().strip():
            messagebox.showerror("Export Error", "Race field cannot be blank.")
            return

        file_path = filedialog.asksaveasfilename(defaultextension=".xlsx", filetypes=[("Excel Files", "*.xlsx"), ("All Files", "*.*")])
        if not file_path:
            return

        # Collect data
        data = []
        for i, tower in enumerate(self.towers):
            # Check if essential fields are filled
            if not tower['Name'].get().strip() and not tower['Damage'].get().strip():
                continue  # Skip this tower if essential fields are empty

            # Safely get Z-Score and Percent Rank or set default values
            z_score = tower.get('Z-Score', tk.StringVar(value="0")).get()
            percent_rank = tower.get('Percent Rank', tk.StringVar(value="0%")).get()

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
                'Z-Score': z_score,  # Safely fetched value
                'Percent Rank': percent_rank,  # Safely fetched value
                'Race': self.race_entry.get(),
                'Tower Number': i+1
            }
            data.append(row)

        if not data:
            messagebox.showinfo("Export", "No tower data to export.")
            return

        df_new = pd.DataFrame(data)

        # Replace empty strings with '0'
        df_new.replace('', '0', inplace=True)

        # Check if file exists
        try:
            df_existing = pd.read_excel(file_path)
            # Remove existing data for the race to overwrite it
            race_name = self.race_entry.get()
            df_existing = df_existing[df_existing['Race'] != race_name]
            # Combine with new data
            df_combined = pd.concat([df_existing, df_new], ignore_index=True)
        except FileNotFoundError:
            df_combined = df_new

        # Write to Excel
        df_combined.to_excel(file_path, index=False)
        messagebox.showinfo("Export", "Data successfully exported.")


    def import_data(self):
        file_path = filedialog.askopenfilename(defaultextension=".xlsx", filetypes=[("Excel Files", "*.xlsx"), ("All Files", "*.*")])
        if not file_path:
            return

        df = pd.read_excel(file_path)

        if 'Race' not in df.columns:
            messagebox.showerror("Import Error", "No 'Race' column found in the data.")
            return

        # Replace '0' with np.nan for empty fields
        df.replace('0', np.nan, inplace=True)

        self.imported_df = df.copy()  # Working DataFrame for temporary changes
        self.original_imported_df = df.copy()  # Preserve original data

        # Get unique races and sort them alphabetically
        races = sorted(df['Race'].dropna().unique().tolist())
        if not races:
            messagebox.showerror("Import Error", "No races found in the data.")
            return

        # Update Combobox
        self.race_combobox['values'] = races
        self.race_combobox.current(0)  # Set default selection

        # Auto-select the first race
        self.on_race_selected(None)

        messagebox.showinfo("Import", "Data imported successfully. Please select a race from the dropdown.")


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
                'Z-Score': tower.get('Z-Score', tk.StringVar()).get(),          # Updated
                'Percent Rank': tower.get('Percent Rank', tk.StringVar()).get(), # Updated
                'Balance Status': tower.get('Balance Status', tk.StringVar()).get(), # Updated
                'Race': self.race_entry.get(),
                'Tower Number': i+1
            }
            data.append(row)

        if data:
            temp_df = pd.DataFrame(data)
            temp_df.to_csv('temp_backup.csv', index=False)


    def on_race_selected(self, event):
        # Save temporary backup
        self.save_temporary_backup()

        selected_race = self.race_combobox.get()

        # Check if imported_df is empty or doesn't contain 'Race' column
        if self.imported_df.empty or 'Race' not in self.imported_df.columns:
            messagebox.showerror("Error", "No data available for the selected race.")
            return

        # Filter the dataframe for the selected race
        df_filtered = self.imported_df[self.imported_df['Race'] == selected_race]

        # Clear existing towers and populate with df_filtered
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
        for i, tower_row in df.iterrows():
            self.add_tower()
            tower_fields = self.towers[-1]
            self.populate_tower_fields(tower_fields, tower_row)

        self.race_entry.delete(0, tk.END)
        self.race_entry.insert(0, df['Race'].iloc[0] if 'Race' in df.columns else '')

        # Update tower numbers
        for idx, tower_fields in enumerate(self.towers):
            self.update_tower_row(tower_fields, idx)

    def open_algorithm_editor(self):
        if self.window_tracker['algorithm_editor'] is not None:
            try:
                self.window_tracker['algorithm_editor'].focus()  # Bring the window to focus if already open
            except tk.TclError:
                # If the window is destroyed, reset the tracker
                self.window_tracker['algorithm_editor'] = None
        else:
            editor = tk.Toplevel(self.root)
            self.window_tracker['algorithm_editor'] = editor  # Track the window
            editor.title("Algorithm Editor")
            editor.geometry("800x900")  # Adjust the window size as needed

            # Bind the destroy event to reset the tracker when the window is closed
            editor.protocol("WM_DELETE_WINDOW", lambda: self.close_window('algorithm_editor', editor))
            editor.bind("<Escape>", lambda event: self.close_window('algorithm_editor', editor))

            # Rest of your window setup code goes here
            tk.Label(editor, text="Calculation Function (Python Code):").grid(row=0, column=0, sticky='nw', padx=10, pady=5)
            self.calc_function_text = tk.Text(editor, height=20, width=90)
            self.calc_function_text.grid(row=1, column=0, padx=10, pady=5, sticky='nsew')

            # Load the calculation function code from self.calc_function_code
            self.calc_function_text.insert(tk.END, self.calc_function_code)

            # Adjusted balance ranges to be displayed vertically
            tk.Label(editor, text="Preset Balance Ranges (Customizable):").grid(row=2, column=0, sticky='nw', padx=10, pady=5)
            self.ranges_text = tk.Text(editor, height=10, width=90)
            self.ranges_text.grid(row=3, column=0, padx=10, pady=5, sticky='nsew')

            # Load current preset ranges
            ranges_code = '{\n' + ',\n'.join([f"    {key}: {value}" for key, value in sorted(self.preset_balance_ranges.items())]) + '\n}'
            self.ranges_text.insert(tk.END, ranges_code)

            # Target Type Balance Adjustments
            tk.Label(editor, text="Target Type Balance Adjustments (Python Dict Format):").grid(row=4, column=0, sticky='nw', padx=10, pady=5)
            self.target_type_adjustments_text = tk.Text(editor, height=5, width=90)
            self.target_type_adjustments_text.grid(row=5, column=0, padx=10, pady=5, sticky='nsew')

            # Load current target type adjustments
            adjustments_code = '{\n' + ',\n'.join([f"    '{key}': {value}" for key, value in self.target_type_balance_adjustments.items()]) + '\n}'
            self.target_type_adjustments_text.insert(tk.END, adjustments_code)

            # Dynamic Balance Range Explanation
            tk.Label(editor, text="Dynamic Balance Range Calculation:").grid(row=6, column=0, sticky='nw', padx=10, pady=5)
            dynamic_calc_text = (
                "Dynamic balance ranges are calculated based on the mean and standard deviation of "
                "DPS per Gold across all towers of the same number and target type. "
                "Outliers are excluded using the Interquartile Range (IQR) method, and a scaling factor "
                "inversely proportional to the tower number is applied."
            )
            dynamic_calc_label = tk.Label(editor, text=dynamic_calc_text, wraplength=600, justify='left')
            dynamic_calc_label.grid(row=7, column=0, padx=10, pady=5, sticky='w')

            # Buttons
            button_frame = ttk.Frame(editor)
            button_frame.grid(row=8, column=0, pady=10)

            save_button = ttk.Button(button_frame, text="Save/Apply", command=self.apply_algorithm_changes)
            save_button.pack(side=tk.LEFT, padx=5)

            save_file_button = ttk.Button(button_frame, text="Save to File", command=self.save_algorithm_to_file)
            save_file_button.pack(side=tk.LEFT, padx=5)

            load_button = ttk.Button(button_frame, text="Load from File", command=self.load_algorithm)
            load_button.pack(side=tk.LEFT, padx=5)

            close_button = ttk.Button(button_frame, text="Close", command=editor.destroy)
            close_button.pack(side=tk.LEFT, padx=5)

            # Edit Dynamic Algorithm Button
            view_dynamic_button = ttk.Button(button_frame, text="View Dynamic Algorithm", command=self.view_dynamic_algorithm)
            view_dynamic_button.pack(side=tk.LEFT, padx=5)

    def apply_algorithm_changes(self):
        errors = []
        # Update calculation function
        calc_code = self.calc_function_text.get("1.0", tk.END)
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
        ranges_code = self.ranges_text.get("1.0", tk.END)
        try:
            self.preset_balance_ranges = eval(ranges_code)
        except Exception as e:
            errors.append(f"Preset balance ranges: {e}")

        # Update target type balance adjustments
        adjustments_code = self.target_type_adjustments_text.get("1.0", tk.END)
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
        file_path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")])
        if not file_path:
            return

        calc_code = self.calc_function_text.get("1.0", tk.END)
        ranges_code = self.ranges_text.get("1.0", tk.END)
        adjustments_code = self.target_type_adjustments_text.get("1.0", tk.END)

        with open(file_path, 'w') as file:
            file.write("# Calculation Function Code\n")
            file.write(calc_code.strip())
            file.write("\n\n# Preset Balance Ranges\n")
            file.write(ranges_code.strip())
            file.write("\n\n# Target Type Balance Adjustments\n")
            file.write(adjustments_code.strip())

        messagebox.showinfo("Saved", "Algorithm and adjustments saved successfully.")

    def load_algorithm(self):
        file_path = filedialog.askopenfilename(defaultextension=".txt", filetypes=[("Text Files", "*.txt"), ("All Files", "*.*")])
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
            self.calc_function_text.delete("1.0", tk.END)
            self.calc_function_text.insert(tk.END, calc_code)

            self.ranges_text.delete("1.0", tk.END)
            self.ranges_text.insert(tk.END, ranges_code)

            self.target_type_adjustments_text.delete("1.0", tk.END)
            self.target_type_adjustments_text.insert(tk.END, adjustments_code)

            messagebox.showinfo("Loaded", "Algorithm and adjustments loaded successfully.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load algorithm:\n{e}")

    def view_dynamic_algorithm(self):
        if self.window_tracker['dynamic_algorithm'] is not None:
            try:
                self.window_tracker['dynamic_algorithm'].focus()  # Bring the window to focus if already open
            except tk.TclError:
                # If the window is destroyed, reset the tracker
                self.window_tracker['dynamic_algorithm'] = None
        else:
            # Open a new window for viewing the dynamic algorithm
            dynamic_editor = tk.Toplevel(self.root)
            self.window_tracker['dynamic_algorithm'] = dynamic_editor  # Track the window
            dynamic_editor.title("View Dynamic Algorithm")
            dynamic_editor.geometry("1100x700")

            # Bind the destroy event to reset the tracker when the window is closed
            dynamic_editor.protocol("WM_DELETE_WINDOW", lambda: self.close_window('dynamic_algorithm', dynamic_editor))
            dynamic_editor.bind("<Escape>", lambda event: self.close_window('dynamic_algorithm', dynamic_editor))

            dynamic_editor.grid_rowconfigure(1, weight=1)
            dynamic_editor.grid_columnconfigure(0, weight=1)

            tk.Label(dynamic_editor, text="Dynamic Balance Range Calculation Code:").grid(row=0, column=0, sticky='nw', padx=10, pady=5)
            self.dynamic_calc_text = tk.Text(dynamic_editor, height=25, width=70)
            self.dynamic_calc_text.grid(row=1, column=0, padx=10, pady=5, sticky='nsew')

            # Load the current dynamic calculation code
            dynamic_code = '''
        # This code calculates dynamic balance ranges based on the mean and standard deviation.
        # Adjust the parameters and methods below to change how dynamic balance ranges are calculated.

        # Outlier Removal: This section uses the Interquartile Range (IQR) method to exclude towers that are extreme outliers.
        # Q1 is the 25th percentile, and Q3 is the 75th percentile. IQR is the difference between Q1 and Q3.
        # Towers with DPS/Gold below (Q1 - 1.5 * IQR) or above (Q3 + 1.5 * IQR) are considered outliers and are excluded.

        if self.dynamic_comparison_var.get() and self.ignore_outliers_var.get():
            Q1 = group['DPS per Gold'].quantile(0.25)
            Q3 = group['DPS per Gold'].quantile(0.75)
            IQR = Q3 - Q1
            filtered_group = group[(group['DPS per Gold'] >= Q1 - 1.5 * IQR) & (group['DPS per Gold'] <= Q3 + 1.5 * IQR)]
            if filtered_group.empty:
                filtered_group = group
        else:
            filtered_group = group

        # Mean and Standard Deviation: After removing outliers, the mean DPS per Gold is calculated for all towers.
        # Standard deviation is used to define how far a tower's DPS/Gold can deviate from the average before it's considered imbalanced.

        mean_dps_per_gold = filtered_group['DPS per Gold'].mean()
        std_dps_per_gold = filtered_group['DPS per Gold'].std(ddof=0)  # Population std

        # Handle Zero Standard Deviation: If all towers have the same DPS per Gold, the standard deviation would be zero.
        # In that case, the algorithm assumes a 10% variation to avoid division errors.

        if std_dps_per_gold == 0:
            std_dps_per_gold = mean_dps_per_gold * 0.1  # Assume 10% variation

        # Define Balance Range: The balance range is defined as the mean ± one standard deviation.
        # Towers with DPS/Gold values within this range are considered balanced.

        low_range = mean_dps_per_gold - std_dps_per_gold
        high_range = mean_dps_per_gold + std_dps_per_gold

        # Scaling Factor: This factor is inversely proportional to the tower number, which means that higher-numbered towers
        # are allowed a slightly wider range for balancing. This helps account for natural progression in tower power.

        scaling_factor = 1 / (tower_num ** 0.02)  # Adjust the exponent to change how the range scales with tower number
        low_range *= scaling_factor
        high_range *= scaling_factor

        # The final balance range is stored in the balance_ranges dictionary for later comparison.
        self.balance_ranges[(tower_num, target_type)] = (low_range, high_range)
        '''

            self.dynamic_calc_text.insert(tk.END, dynamic_code)
            self.dynamic_calc_text.config(state=tk.DISABLED)  # Make the text read-only

    # Rest of your method code...


        # Comments explaining each part
            comments_text = '''
    # Explanation of Key Components:
    # 1. Outlier Removal: This section uses IQR (Interquartile Range) to exclude extreme outliers from the DPS per Gold calculation.
    #    You can modify the IQR multiplier (currently 1.5) to adjust how strict the outlier removal process is.
    # 2. Mean and Standard Deviation: These are used to calculate the average DPS per Gold and its acceptable range.
    # 3. Scaling Factor: As tower numbers increase, this factor slightly widens the acceptable range of balance for more expensive or powerful towers.
    #    Adjusting the exponent (currently 0.02) will impact how much flexibility is allowed for higher-tier towers.
    '''
            tk.Label(dynamic_editor, text=comments_text, justify='left', wraplength=580).grid(row=2, column=0, padx=10, pady=5)

        # Buttons
            button_frame = ttk.Frame(dynamic_editor)
            button_frame.grid(row=3, column=0, pady=10)

            close_button = ttk.Button(button_frame, text="Close", command=dynamic_editor.destroy)
            close_button.pack(side=tk.LEFT, padx=5)


    def show_comparison(self):
        if self.window_tracker['analysis'] is not None:
            try:
                self.window_tracker['analysis'].focus()  # Bring the window to focus if already open
            except tk.TclError:
                # If the window is destroyed, reset the tracker
                self.window_tracker['analysis'] = None
        else:
            comparison_win = tk.Toplevel(self.root)
            self.window_tracker['analysis'] = comparison_win  # Track the window
            comparison_win.title("Analysis")
            comparison_win.geometry("800x600")

            # Bind the destroy event to reset the tracker when the window is closed
            comparison_win.protocol("WM_DELETE_WINDOW", lambda: self.close_window('analysis', comparison_win))
            comparison_win.bind("<Escape>", lambda event: self.close_window('analysis', comparison_win))

            comparison_text = tk.Text(comparison_win, wrap='none')
            comparison_text.pack(fill=tk.BOTH, expand=True)

            # Define tags for comparison_text
            comparison_text.tag_configure("bold", font=("TkDefaultFont", 10, "bold"))
            comparison_text.tag_configure("green", foreground="green")
            comparison_text.tag_configure("red", foreground="red")
            comparison_text.tag_configure("blue", foreground="blue")
            comparison_text.tag_configure("purple", foreground="purple")
            comparison_text.tag_configure("bold_blue", foreground="blue", font=("TkDefaultFont", 10, "bold"))
            comparison_text.tag_configure("bold_red", foreground="red", font=("TkDefaultFont", 10, "bold"))
            comparison_text.tag_configure("bold_green", foreground="green", font=("TkDefaultFont", 10, "bold"))

            # Perform comprehensive analysis
            analysis_result, outliers = self.perform_comparison_analysis()
            comparison_text.insert(tk.END, analysis_result)

            # Append Outlier Section
            if outliers['low'].empty and outliers['high'].empty:
                pass  # No outliers
            else:
                comparison_text.insert(tk.END, "\n" + "="*160 + "\n", ())
                comparison_text.insert(tk.END, "Outlier Analysis:\n", "bold_blue")
                if not outliers['low'].empty:
                    comparison_text.insert(tk.END, "\nLow-End Outliers:\n", "bold_red")
                    for _, row in outliers['low'].iterrows():
                        outlier_str = f"Tower {row['Tower Number']} ({row['Race']}) - DPS/Gold: {self.format_number(row['DPS per Gold'])}\n"
                        comparison_text.insert(tk.END, outlier_str, "red")
                if not outliers['high'].empty:
                    comparison_text.insert(tk.END, "\nHigh-End Outliers:\n", "bold_red")
                    for _, row in outliers['high'].iterrows():
                        outlier_str = f"Tower {row['Tower Number']} ({row['Race']}) - DPS/Gold: {self.format_number(row['DPS per Gold'])}\n"
                        comparison_text.insert(tk.END, outlier_str, "red")

            # Add scrollbars
            y_scroll = ttk.Scrollbar(comparison_win, orient=tk.VERTICAL, command=comparison_text.yview)
            x_scroll = ttk.Scrollbar(comparison_win, orient=tk.HORIZONTAL, command=comparison_text.xview)
            comparison_text.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)
            y_scroll.pack(side=tk.RIGHT, fill=tk.Y)
            x_scroll.pack(side=tk.BOTTOM, fill=tk.X)



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
            self.result_text.delete(1.0, tk.END)

            # Clear the "Race:" text box
            self.race_entry.delete(0, tk.END)

            # Clear the race combobox
            self.race_combobox.set('')

            # Iterate through each tower and reset its fields
            for tower in self.towers:
                self.clear_tower_fields(tower)


if __name__ == "__main__":
    root = tk.Tk()
    app = TowerApp(root)
    root.mainloop()
