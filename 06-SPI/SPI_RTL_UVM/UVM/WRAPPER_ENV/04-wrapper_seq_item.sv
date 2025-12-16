package wrapper_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class wrapper_seq_item extends uvm_sequence_item;
    `uvm_object_utils(wrapper_seq_item);

    rand logic       rst_n, SS_n;
    rand logic       MOSI;
         logic       MISO;
         logic       MISO_gm;

    // Typedef Enum to be descriptive with the operations to be done
    typedef enum bit [2:0] {WRITE_ADDR = 3'b000, WRITE_DATA = 3'b001, READ_ADDR = 3'b110, READ_DATA = 3'b111} e_state;

    rand bit        MOSI_BUS_RAND[];   // Dynamic Array to be randomized every cycle
         bit        MOSI_BUS[];        // Dynamic Array to take randomized values only from MOSI_BUS_RAND every start of communication
         int        ss_n_cnt;          // Counter to indicate Strat and End of communication
         int        count;             // Counter to Serialize the MOSI_BUS bit by bit in MOSI
         int        WIDTH;             // Integer to take only two values 13 (For all Operations except Read_Data) and 23 (For Read_Data)

    // States to model FSM concept
    rand e_state    wrapper_state;     // Randomized every cycle
         e_state    prev_state;        // Not Randomized to take values of wrapper_state only on the start of communication

    rand bit [1:0] mode_control;       // 0: write_only, 1: read_only, 2: write_read

    function new(string name = "wrapper_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s MOSI = %0b, SS_n = %0b, rst_n = %0d, MISO = %0b",
            super.convert2string(),MOSI,SS_n,rst_n,MISO);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("MOSI = %0b, SS_n = %0b, rst_n = %0d",MOSI,SS_n,rst_n);
    endfunction

    // 1- The reset signal (rst_n) shall be deasserted most of the time.
    constraint rst_n_c {rst_n dist {0:/2, 1:/98};}

    // 2- The SS_n signal to be high for one cycle every 13 cycles for all cases except read data to be high for one cycle every 23 cycles
    constraint ss_n_c {
        if (!rst_n) {
            SS_n == 1;  
        } else {
            // SS_n should be LOW during the data transfer (cycles 1-12 or 1-22) and HIGH only at the end (cycle 13 or 23)
            if (prev_state != READ_DATA) {          // For any operations except READ_DATA
                if (ss_n_cnt inside {[0:12]}) {
                    SS_n == 0;          
                } else { // ss_n_cnt == 13
                    SS_n == 1;           
                }
            } else {                                 // For READ_DATA only
                if (ss_n_cnt inside {[0:22]}) {
                    SS_n == 0;           
                } else { // ss_n_cnt == 23
                    SS_n == 1;           
                }
            }
        }
    }

    // 3- Including Constraints 3,4,5 and 6 controlled by mode_select signal to Write-only, Read-only or Write_Read
    constraint write_read_c {
        if (mode_control == 0){                            // Write only Sequence
            wrapper_state inside {WRITE_ADDR,WRITE_DATA};
            if (prev_state == WRITE_DATA)
                wrapper_state == WRITE_ADDR;
        }
        else if(mode_control == 1){                        // Read only Sequence
            wrapper_state inside {READ_ADDR,READ_DATA};
            if (prev_state == READ_DATA)
                wrapper_state == READ_ADDR;
        }
        else if(mode_control == 2){                       // Write/Read Sequence
            wrapper_state inside {WRITE_ADDR,WRITE_DATA,READ_ADDR,READ_DATA};
            if (prev_state == WRITE_ADDR)
                wrapper_state inside {WRITE_ADDR,WRITE_DATA};
            else if (prev_state == WRITE_DATA)
                wrapper_state dist {READ_ADDR :/ 60, WRITE_ADDR :/ 40};
            else if (prev_state == READ_ADDR)
                wrapper_state == READ_DATA;
            else 
                wrapper_state dist {WRITE_ADDR :/ 60, READ_ADDR :/ 40};
        }
    }
    
    // Constraint to Serialize MOSI_BUS on MOSI bit by bit
    constraint mosi_c {
        if (rst_n) {
            if (ss_n_cnt != WIDTH){  // Serialize During communication only
                MOSI == MOSI_BUS[count];
            }
        }
    }

    function void pre_randomize();
        if (!rst_n) begin
            count = 0;
        end
        else begin
            if (ss_n_cnt == 0) begin
                prev_state = wrapper_state; // Will be updated when ss_n_cnt == 0 (start of communication) (after SS_n asserted and de-asserted)
                count = 0;                  // Serialize count git inialized with zero to start communication

                if (prev_state == READ_DATA) begin   // 23 Cycles For Read Data
                    WIDTH = 23;
                    MOSI_BUS = new[WIDTH];
                    MOSI_BUS_RAND = new[WIDTH];
                end
                else begin                           // 13 Cycles For any other state
                    WIDTH = 13;
                    MOSI_BUS = new[WIDTH];
                    MOSI_BUS_RAND = new[WIDTH];
                end
            end
            else begin
                count = count + 1;                   // Increment serializer counter during running of simulation
            end
        end
        // $display("ss_n_cnt = %0d, count = %0d, MOSI_BUS = %0p, MOSI = %0b, prev_state = %03b, wrapper_state = %03b",ss_n_cnt,count,MOSI_BUS,MOSI,prev_state,wrapper_state);
    endfunction
    
    function void post_randomize();
        if (!rst_n) begin
            ss_n_cnt = 0;
        end else begin
            if (ss_n_cnt == 0) begin                  // At the Start of Simulation 
                MOSI_BUS = MOSI_BUS_RAND;             // 1- Take Randomized values from MOSI_BUS_RAND to be assigned tp MOSI_BUS array
                for (int i=0; i<3; i++)               // 2- Loop for the 3 MSB to be like prev_state, which takes value of the required operation to be done
                    MOSI_BUS[i] = prev_state[2-i];
            end
            
            // Handle SS_n counter to control start and end of communication
            if ((ss_n_cnt != 13) && (prev_state != READ_DATA))
                ss_n_cnt += 1;
            else if ((ss_n_cnt != 23) && (prev_state == READ_DATA))
                ss_n_cnt += 1;
            else
                ss_n_cnt = 0;
        end
    endfunction

endclass
endpackage

// Another Sequence Item Solution Corresponding to the Another Sequence

/*
package wrapper_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class wrapper_seq_item extends uvm_sequence_item;
    `uvm_object_utils(wrapper_seq_item);

    rand bit       MOSI, rst_n, SS_n;
         bit       MISO;
         bit       MISO_gm;

    typedef enum bit [2:0] {WRITE_ADDR = 3'b000, WRITE_DATA = 3'b001, READ_ADDR = 3'b110, READ_DATA = 3'b111} e_state;

    rand e_state      wrapper_state;
         e_state      prev_state;
    rand bit   [12:0] MOSI_BUS;

         bit rd_data_flag;
    rand bit read_add_sent;
         int ss_n_cnt, write_cnt;

    function new(string name = "wrapper_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s MOSI = %0b, SS_n = %0b, rst_n = %0d, MISO = %0b",
            super.convert2string(),MOSI,SS_n,rst_n,MISO);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("MOSI = %0b, SS_n = %0b, rst_n = %0d",MOSI,SS_n,rst_n);
    endfunction

    function void pre_randomize(); // For Debugging
        $display("rstn = %0b, ss_n = %0b, MOSI = %0b, ss_n_cnt = %0d, write_cnt = %0d, MOSI_BUS = %011b, prev_state = %03b, wrapper_state = %03b, read_add_sent = %0b, rd_data_flag = %0b",rst_n, SS_n, MOSI,ss_n_cnt,write_cnt,MOSI_BUS,prev_state,wrapper_state,read_add_sent,rd_data_flag);
    endfunction

    function void post_randomize();
        if (rst_n) begin
            // SS_n = 0 (Comm. ON) Counter and if Counter = 0 (Comm. OFF)
            if ((ss_n_cnt != 13) && (!read_add_sent))
                ss_n_cnt += 1;
            else if ((ss_n_cnt != 23) && (read_add_sent))
                ss_n_cnt += 1;
            else
                ss_n_cnt = 0;
            // For Serialize MOSI to Design Counter through MOSI_BUS 
            if (ss_n_cnt == 0)
                write_cnt = 0;
            else begin
                if (write_cnt != 12) 
                    write_cnt += 1;
                else
                    write_cnt = 0;
            end
            // Store the Wrapper_State to the Prev_State
            if (ss_n_cnt == 0) begin
                if (wrapper_state != READ_DATA) begin
                    prev_state = wrapper_state;
                    rd_data_flag = 0;
                end
                else if (wrapper_state == READ_DATA) begin
                    prev_state = wrapper_state;
                    rd_data_flag = 1;
                end
            end
        end
        else begin
            ss_n_cnt = 0;
            write_cnt = 0;
            rd_data_flag = 0;
            prev_state = e_state'(0);
        end
    endfunction

    constraint rst_n_c {rst_n dist {0:/2, 1:/98};}

    constraint write_c {
        read_add_sent == 0;
        if (rst_n) {
            if (ss_n_cnt == 13) {
                if (prev_state == WRITE_ADDR)
                    wrapper_state == WRITE_DATA;
                else
                    wrapper_state inside {WRITE_ADDR, WRITE_DATA};
            }
        }
        else {
            wrapper_state == e_state'(0);
        }
    }

    constraint read_c {
        if (rst_n) {
            if (prev_state == READ_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13) 
                    wrapper_state == READ_DATA;
            }
            else if (prev_state == READ_DATA) {
                if (rd_data_flag) {
                    read_add_sent == 1;
                    if (ss_n_cnt == 23)
                         wrapper_state == READ_ADDR;
                }
                else {
                    read_add_sent == 0;
                    if (ss_n_cnt == 13)
                         wrapper_state == READ_DATA;
                }
            }
            else {
                read_add_sent == 0;
                wrapper_state == READ_ADDR;
            }
        }
        else {
            read_add_sent == 0;
            wrapper_state == e_state'(0);
        }
    }

    constraint write_read_c {
        if (rst_n) {
            if (prev_state == WRITE_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13)
                    wrapper_state == WRITE_DATA;
            }
            else if (prev_state == WRITE_DATA) {
                read_add_sent == 0;
                if (ss_n_cnt == 13) 
                    wrapper_state dist {READ_ADDR :/ 60, WRITE_ADDR :/ 40};
            }
            else if (prev_state == READ_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13)
                    wrapper_state == READ_DATA;
            }
            else if (prev_state == READ_DATA) {
                if (rd_data_flag) {
                    read_add_sent == 1;
                    if (ss_n_cnt == 23)
                        wrapper_state dist {WRITE_ADDR :/ 60, READ_ADDR :/ 40};
                }
                else {
                    read_add_sent == 0;
                    if (ss_n_cnt == 13)
                        wrapper_state == READ_DATA;
                }
            }
            else {
                read_add_sent == 0;
                wrapper_state == READ_ADDR;
            }
        }
        else {
            read_add_sent == 0;
            wrapper_state == e_state'(0);
        }
    }

    constraint mosi_c {
        if (rst_n) {
            MOSI_BUS[11:9] == prev_state;
            if ((write_cnt != 12) && !SS_n)
                MOSI == MOSI_BUS[12-write_cnt];
        }
    }

    constraint ss_n_c {
        if (rst_n) {
            if ((ss_n_cnt != 13) && (prev_state != READ_DATA))
                SS_n == 0;
            else if ((ss_n_cnt != 23) && (prev_state == READ_DATA))
                SS_n == 0;
            else
                SS_n == 1;
        }
    }
endclass
endpackage
*/
