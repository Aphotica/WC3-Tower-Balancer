Warcraft III Tower Balancer
**Created for use in Wintermaul Wars maps on Warcraft III, though should work in any Tower Defense game on WC3. WmW Discord: https://discord.gg/Qsg6UDn**

**HOW TO USE**
1) Add the tower data for your race and give your race a name. If any tower fields don't apply, leave them blank.
2) Export your race data for each race before hitting "Clear All" and adding additional races.
   **You can export and work out of the same Excel file. As long as the race names are the same, any updates will override it.
4) The more races and towers you add, the more accurate the dynamic algorithm becomes (recommend a minimum of 10 races)
5) Use the Algorithm Editor to adjust the preset balance ranges (and algorithm itself) to your needs if using < 10 races.
  
6) When all races and towers are completed and exported into one CSV, import them back into the program.
7) A comprehensive view of the tower data will calculate. The outliers (weakest/strongest) will populate at the bottom
8) Begin implementing changes to your towers as needed, exporting after each race to update the tower values.

9) For a tower to be balanced, its DPS/Gold must be within the balance range (+/- 1 SD), have a Z-score between -1 to 1, with a percentile rank between 40-60% (disregard if data set is small)

NOTE: To retain modified data while flipping through races, a temp_backup.csv is created in the exe location to recall the data. Delete this when no longer needed.


**Further Details:**

**1. DPS per Gold within Balance Range:**
The algorithm calculates a balance range for each tower, defined as the mean DPS per gold ± one standard deviation.
A tower is considered balanced if its DPS per gold falls within this balance range.
The balance range can be dynamically calculated based on the current data set (dynamic algorithm) or preset based on predefined ranges.
**DPS per Gold is multiplied by 100 to achieve realistic whole numbers.**

**2. Z-Score:**
The Z-score measures how far the tower's DPS per gold is from the mean DPS per gold in terms of standard deviations.
A tower is considered balanced if its Z-score falls between -1 and 1, which means the tower's DPS per gold is within one standard deviation from the average.
Z-scores outside this range indicate the tower is either underpowered (Z < -1) or overpowered (Z > 1).

**3. Percentile Rank (ignore with small data sets):**
The percentile rank shows where the tower's DPS per gold falls compared to other towers, expressed as a percentage.
A tower is considered balanced if its percentile rank is between 40% and 60%. This indicates the tower is near the middle of the distribution of DPS per gold.
Towers with very high or very low percentile ranks are considered overpowered or underpowered, respectively.

**4. Dynamic Balance Range for Target Types:**
For towers with different target types (e.g., "Ground Splash," "Air Splash"), the balance range is dynamically adjusted.

Air Splash or Ground Splash towers populate with two different balance ranges:
  a) one with splash (against target type) with a dynamic range 1.5x above the "All" target data
  b) one without splash (against non-target type) with a dynamic range 50% below the "All" target data
This ensures that races that specialize in Ground or Air Splash will have the power to perform where they are meant to be strongest, yet have a noticeable tradeoff in single-target DPS compared to their peers.


**6. Outlier Consideration:**
If the user enables "Ignore Outliers," the algorithm will exclude extreme outliers using the interquartile range (IQR) method. A tower's DPS per gold is only considered for balance calculations if it is not an outlier.

**If curious, feel free to view the algorithm to see if the script will work for you. The code is open source, so feel free to use it however you need.**

**ALGORITHM**

#def calculate_dps_per_gold(base_damage, dice, sides_per_die, cooldown, range_val,
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


**DYNAMIC ALGORITHM**

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
