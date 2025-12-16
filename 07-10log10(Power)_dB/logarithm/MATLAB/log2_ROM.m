clc
clear
close all

% Run the main generation for 1024 LUT
generate_log2_lut_10000_1024();

% Uncomment to run precision analysis
analyze_precision_improvement();

% Uncomment to run comparison
compare_scales_1024();

% Uncomment to create test vectors
create_test_vectors_1024();

function generate_log2_lut_10000_1024()
    % Generate LUT for log2(1 + k/1024) scaled by 10000
    
    fprintf('=== Generating 1024-entry Log2 LUT Scaled by 10000 ===\n');
    
    num_entries = 1024;
    scale_factor = 10000;
    
    for k = 0:num_entries-1
        % Calculate log2(1 + k/1024) with high precision
        fraction = k / 1024;
        if k == 0
            log_val = 0;
        else
            log_val = log2(1 + fraction);
        end
        
        % Scale by 10000 and round
        scaled_val = round(log_val * scale_factor);
        
        % Ensure it fits in 24 bits (max value 16777215)
        if scaled_val >= 2^24
            scaled_val = 2^24 - 1;
        end
        
        % Format for Verilog
        if mod(k, 8) == 0
            if k > 0
                fprintf('\n');
            end
            fprintf('    ');
        end
        
        fprintf('ROM[%d] <= 24''d%d; ',k,scaled_val);
        
    end
    fprintf('\n');
    fprintf('\n// LUT for log2(1 + k/1024) * 10000\n');
    fprintf('localparam reg [23:0] LUT [0:1023] = ''{\n');
    for k = 0:num_entries-1
        % Calculate log2(1 + k/1024) with high precision
        fraction = k / 1024;
        if k == 0
            log_val = 0;
        else
            log_val = log2(1 + fraction);
        end
        
        % Scale by 10000 and round
        scaled_val = round(log_val * scale_factor);
        
        % Ensure it fits in 24 bits (max value 16777215)
        if scaled_val >= 2^24
            scaled_val = 2^24 - 1;
        end
        
        % Format for Verilog
        if mod(k, 8) == 0
            if k > 0
                fprintf('\n');
            end
            fprintf('    ');
        end
        
        if k == num_entries-1
            fprintf('24''d%-8d', scaled_val);
        else
            fprintf('24''d%-8d, ', scaled_val);
        end
    end
    
    fprintf('\n};\n');
    
    % Verification of key values
    fprintf('\n=== Key Value Verification (1024 LUT, 10000 scale) ===\n');
    test_points = [0, 1, 64, 128, 256, 512, 768, 1023];
    for k = test_points
        if k == 0
            exact = 0;
        else
            exact = log2(1 + k/1024);
        end
        scaled_exact = exact * 10000;
        rounded = round(scaled_exact);
        fprintf('k=%4d: log2(1+%4d/1024) = %.6f * 10000 = %8.1f -> %d\n', ...
                k, k, exact, scaled_exact, rounded);
    end
    
    % Test the algorithm with 1024 LUT
    fprintf('\n=== Algorithm Test with 1024 LUT ===\n');
    test_values = [1, 2, 3, 4, 5, 7, 8, 15, 16, 255, 256, 1024, 2048, 4096];
    
    for val = test_values
        if val == 0
            expected = 0;
            int_part_expected = 0;
            frac_part_expected = 0;
        else
            expected = log2(val);
            int_part_expected = floor(expected);
            frac_part_expected = expected - int_part_expected;
        end
        scaled_frac_expected = round(frac_part_expected * 10000);
        
        fprintf('Value: %4d, Expected: %8.6f = %d + %.6f (scaled: %d)\n', ...
                val, expected, int_part_expected, frac_part_expected, scaled_frac_expected);
    end
end

% Alternative: Generate with verification against 2^24 scale for 1024 LUT
function compare_scales_1024()
    fprintf('\n=== Comparing 10000 vs 2^24 Scale (1024 LUT) ===\n');
    
    num_entries = 1024;
    scale_10000 = 10000;
    scale_2_24 = 2^24;
    
    fprintf('k\tlog2(1+k/1024)\t10000 Scale\t2^24 Scale\tRatio\n');
    fprintf('-\t-------------\t-----------\t----------\t-----\n');
    
    for k = [0, 1, 64, 128, 256, 512, 768, 1023]
        if k == 0
            log_val = 0;
        else
            log_val = log2(1 + k/1024);
        end
        
        scaled_10000 = round(log_val * scale_10000);
        scaled_2_24 = round(log_val * scale_2_24);
        ratio = scaled_2_24 / scaled_10000;
        
        fprintf('%4d\t%11.6f\t%11d\t%10d\t%.2f\n', ...
                k, log_val, scaled_10000, scaled_2_24, ratio);
    end
end

% Function to create test vectors for verification with 1024 LUT
function create_test_vectors_1024()
    fprintf('\n=== Creating Test Vectors for 1024 LUT ===\n');
    
    test_values = [1, 2, 3, 4, 5, 7, 8, 15, 16, 32, 64, 128, 255, 256, 512, 1024, 2048, 4096];
    
    fprintf('Input\tExpected log2\tInteger\tFraction (10000 scale)\n');
    fprintf('-----\t-------------\t-------\t----------------------\n');
    
    for val = test_values
        if val == 0
            expected = 0;
            int_part = 0;
            frac_part = 0;
        else
            expected = log2(val);
            int_part = floor(expected);
            frac_part = expected - int_part;
        end
        scaled_frac = round(frac_part * 10000);
        
        fprintf('%5d\t%12.6f\t%7d\t%21d\n', ...
                val, expected, int_part, scaled_frac);
    end
end

% Additional function to show precision improvement
function analyze_precision_improvement()
    fprintf('\n=== Precision Improvement Analysis (256 vs 1024 LUT) ===\n');
    
    % Compare quantization error for both LUT sizes
    test_points = [1, 2, 3, 4, 5, 7, 8, 15, 16, 32, 64, 128, 255, 256];
    
    fprintf('Value\tExact\t\t256-LUT Error\t1024-LUT Error\tImprovement\n');
    fprintf('-----\t-----\t\t------------\t-------------\t-----------\n');
    
    for val = test_points
        if val == 0
            continue;
        end
        
        exact = log2(val);
        int_part = floor(exact);
        frac_part = exact - int_part;
        
        % 256 LUT quantization
        k_256 = round(frac_part * 256);
        frac_256 = log2(1 + k_256/256);
        error_256 = abs(frac_part - frac_256);
        
        % 1024 LUT quantization  
        k_1024 = round(frac_part * 1024);
        frac_1024 = log2(1 + k_1024/1024);
        error_1024 = abs(frac_part - frac_1024);
        
        improvement = (error_256 - error_1024) * 10000; % in scaled units
        
        fprintf('%5d\t%8.6f\t%12.6f\t%13.6f\t%11.2f\n', ...
                val, exact, error_256, error_1024, improvement);
    end
end
