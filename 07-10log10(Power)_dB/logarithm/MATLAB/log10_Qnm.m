clc
clear all
close all

%% Test Parameters
tests = 100;

% Different quantization formats to test
formats = [
    struct('n', 16, 'm', 16, 'color', 'r', 'name', 'Q16.16');
    struct('n', 8, 'm', 24, 'color', 'b', 'name', 'Q8.24');
    struct('n', 12, 'm', 20, 'color', 'g', 'name', 'Q12.20');
];

%% Initialize arrays
relative_errors = zeros(tests, length(formats));
absolute_errors = zeros(tests, length(formats));
db_errors = zeros(tests, length(formats));

%% Run tests
for i = 1 : tests
    x = randi([1, 1000], 1, 1);
    true_value = log10(x);
    
    for j = 1 : length(formats)
        fmt = formats(j);
        
        % Convert to fixed-point
        y_fixed = fi(true_value, 1, fmt.n + fmt.m, fmt.m);
        
        % Compute errors
        absolute_errors(i, j) = abs(double(y_fixed) - true_value);
        relative_errors(i, j) = absolute_errors(i, j) / abs(true_value);
        
        % Error in dB: 20*log10(1 + relative_error)
        db_errors(i, j) = 20 * log10(1 + relative_errors(i, j));
    end
end

%% Plot Results
figure;
% Plot 1: Absolute Errors
subplot(2, 2, 1);
hold on;
for j = 1 : length(formats)
    plot(absolute_errors(:, j), formats(j).color, 'linewidth', 2, 'DisplayName', formats(j).name);
end
ylabel('Absolute Error');
xlabel('Test Case');
title('Absolute Error Comparison');
legend('show');
grid on;

% Plot 2: Relative Errors
subplot(2, 2, 2);
hold on;
for j = 1 : length(formats)
    plot(relative_errors(:, j) * 100, formats(j).color, 'linewidth', 2, 'DisplayName', formats(j).name);
end
ylabel('Relative Error (%)');
xlabel('Test Case');
title('Relative Error Comparison');
legend('show');
grid on;

% Plot 3: Errors in dB
subplot(2, 2, 3);
hold on;
for j = 1 : length(formats)
    plot(db_errors(:, j), formats(j).color, 'linewidth', 2, 'DisplayName', formats(j).name);
end
ylabel('Error (dB)');
xlabel('Test Case');
title('Error in dB (20*log10(1 + relative error))');
legend('show');
grid on;

%% Statistical Analysis
fprintf('\n========================================================\n');
fprintf('STATISTICAL ANALYSIS OF LOG10 QUANTIZATION ERRORS \n');
fprintf('========================================================\n\n');

for j = 1:length(formats)
    mean_db_error = mean(db_errors(:, j));
    max_db_error = max(db_errors(:, j));
    
    fprintf('%s:\n', formats(j).name);
    fprintf('  Mean dB Error = %.4f dB\n', mean_db_error);
    fprintf('  Max dB Error  = %.4f dB\n', max_db_error);
    
    % Check if format meets 0.1 dB specification
    if max_db_error < 0.1
        fprintf('  Status: ✓ PASS (All tests < 0.1 dB)\n');
    else
        fprintf('  Status: ✗ FAIL (Some tests > 0.1 dB)\n');
    end
    fprintf('--------------------------------------------------------\n');
end

%% LUT Generation Parameters
lut_size = 1024;           % Reduced LUT size for practical implementation
bits_per_entry = 32;       % Q8.24 format

%% Generate reduced LUT using range reduction
% We'll create a LUT for values 1-1024 and use range reduction for larger values
fprintf('Generating LUT for log10(x) in Q8.24 format...\n');

% Create LUT for x = 1 to lut_size
lut = zeros(1, lut_size);
for x = 1:lut_size
    true_value = log10(x);
    % Convert to Q8.24 fixed-point
    q8_24_value = int32(true_value * 2^24);
    lut(x) = double(q8_24_value) / 2^24;  % Store as double for verification
end

%% Test the LUT implementation
tests = 100;
relative_errors = zeros(1, tests);
absolute_errors = zeros(1, tests);
db_errors = zeros(1, tests);
test_values = zeros(1, tests);

fprintf('Testing LUT implementation...\n');

for i = 1:tests
    % Generate random 32-bit input
    x = randi([1, (2^32)-1], 1, 1);
    test_values(i) = x;
    true_value = log10(x);
    
    % LUT-based calculation with range reduction
    if x <= lut_size
        % Direct LUT access
        lut_value = lut(x);
    else
        % Range reduction: x = mantissa * 10^exponent
        % Find mantissa in [1, lut_size] range
        mantissa = x;
        exponent = 0;
        
        while mantissa > lut_size
            mantissa = floor(mantissa / 10);
            exponent = exponent + 1;
        end
        
        % log10(x) = log10(mantissa) + exponent
        lut_value = lut(mantissa) + exponent;
    end
    
    % Compute errors
    absolute_errors(i) = abs(lut_value - true_value);
    relative_errors(i) = absolute_errors(i) / abs(true_value);
    db_errors(i) = 20 * log10(1 + relative_errors(i));
end

%% Plot Results
figure('Position', [100, 100, 1200, 800]);

% Plot 1: Absolute Errors
subplot(2, 2, 1);
plot(absolute_errors, 'b', 'linewidth', 2);
ylabel('Absolute Error');
xlabel('Test Case');
title('Absolute Error - LUT Q8.24');
grid on;

% Plot 2: Relative Errors
subplot(2, 2, 2);
plot(relative_errors * 100, 'r', 'linewidth', 2);
ylabel('Relative Error (%)');
xlabel('Test Case');
title('Relative Error - LUT Q8.24');
grid on;

% Plot 3: Errors in dB
subplot(2, 2, 3);
plot(db_errors, 'g', 'linewidth', 2);
hold on;
plot([1, tests], [0.1, 0.1], 'k--', 'linewidth', 2, 'DisplayName', '0.1 dB Spec');
ylabel('Error (dB)');
xlabel('Test Case');
title('Error in dB - LUT Q8.24');
legend('Error', '0.1 dB Spec', 'Location', 'best');
grid on;

% Plot 4: Error Distribution
subplot(2, 2, 4);
histogram(db_errors, 20, 'FaceColor', 'm', 'EdgeColor', 'black');
xlabel('Error (dB)');
ylabel('Frequency');
title('Error Distribution - LUT Q8.24');
grid on;

%% Statistical Analysis
fprintf('\n========================================================\n');
fprintf('STATISTICAL ANALYSIS OF LUT Q8.24 IMPLEMENTATION\n');
fprintf('========================================================\n\n');

mean_abs_error = mean(absolute_errors);
max_abs_error = max(absolute_errors);
mean_rel_error = mean(relative_errors) * 100;
max_rel_error = max(relative_errors) * 100;
mean_db_error = mean(db_errors);
max_db_error = max(db_errors);

fprintf('LUT Size: %d entries\n', lut_size);
fprintf('Input Range: 0 to %d\n', (2^32)-1);
fprintf('Output Format: Q8.24\n\n');

fprintf('Absolute Error:\n');
fprintf('  Mean = %.6f\n', mean_abs_error);
fprintf('  Max  = %.6f\n', max_abs_error);
fprintf('\n');

fprintf('Relative Error:\n');
fprintf('  Mean = %.4f%%\n', mean_rel_error);
fprintf('  Max  = %.4f%%\n', max_rel_error);
fprintf('\n');

fprintf('Error in dB:\n');
fprintf('  Mean = %.4f dB\n', mean_db_error);
fprintf('  Max  = %.4f dB\n', max_db_error);
fprintf('\n');

if max_db_error < 0.1
    fprintf('Status: ✓ PASS - All tests < 0.1 dB specification\n');
else
    fprintf('Status: ✗ FAIL - Some tests > 0.1 dB specification\n');
end

%% Additional analysis for different LUT sizes
fprintf('\n========================================================\n');
fprintf('LUT SIZE ANALYSIS FOR 0.1 dB SPECIFICATION\n');
fprintf('========================================================\n\n');

lut_sizes = [256, 512, 1024, 2048, 4096];
max_errors = zeros(1, length(lut_sizes));

for size_idx = 1:length(lut_sizes)
    current_lut_size = lut_sizes(size_idx);
    
    % Test with current LUT size
    test_errors = zeros(1, 50);
    for i = 1:50
        x = randi([1, (2^32)-1], 1, 1);
        true_value = log10(x);
        
        % LUT calculation with range reduction
        if x <= current_lut_size
            lut_val = log10(x);  % Perfect for LUT range
        else
            mantissa = x;
            exponent = 0;
            while mantissa > current_lut_size
                mantissa = floor(mantissa / 10);
                exponent = exponent + 1;
            end
            lut_val = log10(mantissa) + exponent;
        end
        
        rel_error = abs(lut_val - true_value) / abs(true_value);
        test_errors(i) = 20 * log10(1 + rel_error);
    end
    
    max_errors(size_idx) = max(test_errors);
    
    if max_errors(size_idx) < 0.1
        status_char = '✓';
    else
        status_char = '✗';
    end
    fprintf('LUT Size: %4d -> Max dB Error: %.4f dB %s\n', ...
            current_lut_size, max_errors(size_idx), status_char);
end

%% Plot LUT size vs error
figure;
plot(lut_sizes, max_errors, 'ro-', 'linewidth', 2, 'markersize', 8);
hold on;
plot([min(lut_sizes), max(lut_sizes)], [0.1, 0.1], 'k--', 'linewidth', 2);
xlabel('LUT Size (entries)');
ylabel('Maximum Error (dB)');
title('LUT Size vs Maximum Error');
legend('Maximum Error', '0.1 dB Specification', 'Location', 'best');
grid on;

% Find recommended LUT size
valid_sizes = lut_sizes(max_errors < 0.1);
if ~isempty(valid_sizes)
    fprintf('\nRecommended LUT size for < 0.1 dB error: start from %d entries\n', min(valid_sizes));
else
    fprintf('\nNo LUT size meets < 0.1 dB error specification. Consider larger LUT or different approach.\n');
end
