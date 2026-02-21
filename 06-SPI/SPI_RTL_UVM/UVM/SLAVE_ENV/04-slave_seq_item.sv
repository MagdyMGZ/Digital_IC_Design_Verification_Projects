package slave_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class slave_seq_item extends uvm_sequence_item;
    `uvm_object_utils(slave_seq_item);

    rand logic       MOSI, rst_n, SS_n, tx_valid;
    rand logic [7:0] tx_data;
         logic [9:0] rx_data;
         logic       rx_valid, MISO;

         logic [9:0] rx_data_gm;
         logic       rx_valid_gm, MISO_gm;

    // Typedef Enum to be descriptive with the operations to be done
    typedef enum bit [2:0] {WRITE_ADDR = 3'b000, WRITE_DATA = 3'b001, READ_ADDR = 3'b110, READ_DATA = 3'b111} e_state;

    rand bit        MOSI_BUS_RAND[];             // Dynamic Array to be randomized every cycle
         bit        MOSI_BUS[];                  // Dynamic Array to take randomized values only from MOSI_BUS_RAND every start of communication
         int        ss_n_cnt;                    // Counter to indicate Strat and End of communication
         int        count;                       // Counter to Serialize the MOSI_BUS bit by bit in MOSI
         int        WIDTH;                       // Integer to take only two values 13 (For all Operations except Read_Data) and 23 (For Read_Data)

    // States to model FSM concept
    rand e_state    slave_state;                 // Randomized every cycle
         e_state    prev_state;                  // Not Randomized to take values of slave_state only on the start of communication


    function new(string name = "slave_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s MOSI = %0b, SS_n = %0b, rst_n = %0d, tx_valid = %0b, tx_data = %0d, rx_data = %0d, rx_valid = %0b, MISO = %0b",
            super.convert2string(),MOSI,SS_n,rst_n,tx_valid,tx_data,rx_data,rx_valid,MISO);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("MOSI = %0b, SS_n = %0b, rst_n = %0d, tx_valid = %0b, tx_data = %0d",MOSI,SS_n,rst_n,tx_valid,tx_data);
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

    // 3- Declare a randomized array to drive bit by bit the MOSI and the first 3 bits sent serially to the MOSI 
    //    when the SS_n falls are valid combinations only (000, 001, 110, 111)
    constraint write_read_c {                       
        slave_state inside {WRITE_ADDR,WRITE_DATA,READ_ADDR,READ_DATA};
        if (prev_state == WRITE_ADDR)
            slave_state inside {WRITE_ADDR,WRITE_DATA};
        else if (prev_state == WRITE_DATA)
            slave_state dist {WRITE_ADDR:/40, READ_ADDR:/60};
        else if (prev_state == READ_ADDR)
            slave_state inside {WRITE_ADDR,READ_DATA};
        else 
            slave_state dist {WRITE_ADDR:/60, READ_ADDR:/40};
    }

    // Constraint to Serialize MOSI_BUS on MOSI bit by bit
    constraint mosi_c {
        if (rst_n) {
            if (ss_n_cnt != WIDTH){  // Serialize During communication only
                MOSI == MOSI_BUS[count];
            }
        }
    }

    // 4- The tx_valid signal to be high in case of read data
    constraint tx_valid_c {
        if (rst_n && !SS_n) {
            if ((prev_state == READ_DATA) && (ss_n_cnt > 12))
                tx_valid == 1;
            else
                tx_valid == 0;
        }
    }
        
    function void pre_randomize();
        if (!rst_n) begin
            count = 0;
        end
        else begin
            if (ss_n_cnt == 0) begin
                prev_state = slave_state;            // Will be updated when ss_n_cnt == 0 (start of communication) (after SS_n asserted and de-asserted)
                count = 0;                           // Serialize count git inialized with zero to start communication

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
       // $display("ss_n_cnt = %0d, count = %0d, MOSI_BUS = %0p, MOSI = %0b, prev_state = %03b, slave_state = %03b",ss_n_cnt,count,MOSI_BUS,MOSI,prev_state,slave_state);
    endfunction

    function void post_randomize();
        if (!rst_n) begin
            ss_n_cnt = 0;
        end else begin
            if (ss_n_cnt == 0) begin          // At the Start of Simulation 
                MOSI_BUS = MOSI_BUS_RAND;     // 1- Take Randomized values from MOSI_BUS_RAND to be assigned tp MOSI_BUS array
                for (int i=0; i<3; i++)       // 2- Loop for the 3 MSB to be like prev_state, which takes value of the required operation to be done
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
package slave_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class slave_seq_item extends uvm_sequence_item;
    `uvm_object_utils(slave_seq_item);

    rand logic       MOSI, rst_n, SS_n, tx_valid;
    rand logic [7:0] tx_data;
         logic [9:0] rx_data;
         logic       rx_valid, MISO;

         logic [9:0] rx_data_gm;
         logic       rx_valid_gm, MISO_gm;

    typedef enum bit [2:0] {WRITE_ADDR = 3'b000, WRITE_DATA = 3'b001, READ_ADDR = 3'b110, READ_DATA = 3'b111} e_state;

    rand e_state      slave_state;
         e_state      prev_state;
    rand bit   [12:0] MOSI_BUS;

         bit rd_data_flag;
    rand bit read_add_sent;
         int ss_n_cnt, write_cnt;

    function new(string name = "slave_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s MOSI = %0b, SS_n = %0b, rst_n = %0d, tx_valid = %0b, tx_data = %0d, rx_data = %0d, rx_valid = %0b, MISO = %0b",
            super.convert2string(),MOSI,SS_n,rst_n,tx_valid,tx_data,rx_data,rx_valid,MISO);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("MOSI = %0b, SS_n = %0b, rst_n = %0d, tx_valid = %0b, tx_data = %0d",MOSI,SS_n,rst_n,tx_valid,tx_data);
    endfunction
        
    function void pre_randomize(); // For Debugging
        // $display("rstn = %0b, ss_n = %0b, MOSI = %0b, ss_n_cnt = %0d, write_cnt = %0d, MOSI_BUS = %011b, prev_state = %03b, slave_state = %03b, read_add_sent = %0b, rd_data_flag = %0b",rst_n, SS_n, MOSI,ss_n_cnt,write_cnt,MOSI_BUS,prev_state,slave_state,read_add_sent,rd_data_flag);
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
            // Store the slave_State to the Prev_State
            if (ss_n_cnt == 0) begin
                if (slave_state != READ_DATA) begin
                    prev_state = slave_state;
                    rd_data_flag = 0;
                end
                else if (slave_state == READ_DATA) begin
                    prev_state = slave_state;
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
        if (rst_n) {
            read_add_sent == 0;
            if (ss_n_cnt == 13) {
                if (prev_state == WRITE_ADDR)
                    slave_state == WRITE_DATA;
                else
                    slave_state inside {WRITE_ADDR, WRITE_DATA};
            }
        }
        else {
            read_add_sent == 0;
            slave_state == e_state'(0);
        }
    }

    constraint read_c {
        if (rst_n) {
            if (prev_state == READ_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13) 
                    slave_state == READ_DATA;
            }
            else if (prev_state == READ_DATA) {
                if (rd_data_flag) {
                    read_add_sent == 1;
                    if (ss_n_cnt == 23)
                         slave_state == READ_ADDR;
                }
                else {
                    read_add_sent == 0;
                    if (ss_n_cnt == 13)
                         slave_state == READ_DATA;
                }
            }
            else {
                read_add_sent == 0;
                slave_state == READ_ADDR;
            }
        }
        else {
            read_add_sent == 0;
            slave_state == e_state'(0);
        }
    }

    constraint write_read_c {
        if (rst_n) {
            if (prev_state == WRITE_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13)
                    slave_state == WRITE_DATA;
            }
            else if (prev_state == WRITE_DATA) {
                read_add_sent == 0;
                if (ss_n_cnt == 13) 
                    slave_state dist {READ_ADDR :/ 60, WRITE_ADDR :/ 40};
            }
            else if (prev_state == READ_ADDR) {
                read_add_sent == 0;
                if (ss_n_cnt == 13)
                    slave_state == READ_DATA;
            }
            else if (prev_state == READ_DATA) {
                if (rd_data_flag) {
                    read_add_sent == 1;
                    if (ss_n_cnt == 23)
                        slave_state dist {WRITE_ADDR :/ 60, READ_ADDR :/ 40};
                }
                else {
                    read_add_sent == 0;
                    if (ss_n_cnt == 13)
                        slave_state == READ_DATA;
                }
            }
            else {
                read_add_sent == 0;
                slave_state == READ_ADDR;
            }
        }
        else {
            read_add_sent == 0;
            slave_state == e_state'(0);
        }
    }

    constraint mosi_c {
        if (rst_n) {
            MOSI_BUS[11:9] == prev_state;
            if ((write_cnt != 12) && !SS_n)
                MOSI == MOSI_BUS[12-write_cnt];
        }
    }

    constraint tx_valid_c {
        if (rst_n && !SS_n) {
            if ((prev_state == READ_DATA) && (ss_n_cnt > 12))
                tx_valid == 1;
            else
                tx_valid == 0;
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
