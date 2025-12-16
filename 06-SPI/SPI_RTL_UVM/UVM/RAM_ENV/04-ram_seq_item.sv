package ram_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"
class ram_seq_item extends uvm_sequence_item;
    `uvm_object_utils(ram_seq_item);

    typedef enum bit [1:0] {WRITE_ADDR = 2'b00, WRITE_DATA = 2'b01, READ_ADDR = 2'b10, READ_DATA = 2'b11} e_state;
    
    rand  logic [9:0] din;
    rand  logic       rx_valid;
    rand  logic       rst_n;
          logic [7:0] dout;
          logic       tx_valid;
          logic [7:0] dout_gm;
          logic       tx_valid_gm;
          
    rand  e_state mem_state;
          e_state prev_state;

    function new(string name = "ram_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s din = %0b, rx_valid = %0d, rst_n = %0d, dout = %0d, tx_valid = %0d",
            super.convert2string(),din,rx_valid,rst_n,dout,tx_valid);
    endfunction
    
    function string convert2string_stimulus();
        return $sformatf ("din = %0b, rx_valid = %0d, rst_n = %0d",din,rx_valid,rst_n);
    endfunction

    // 1- The reset signal (rst_n) shall be deasserted most of the time.
    constraint rst_n_c {rst_n dist {0:/2, 1:/98};}

    // 2- The rx_valid signal shall be asserted most of time.
    constraint rx_valid_c {rx_valid dist {0:/10, 1:/90};}

    // 3- For a write-only sequence, every Write Address operation shall always be followed by either Write Address or Write Data operation.
    constraint write_c {
        if (rst_n && rx_valid) {
            if (prev_state == WRITE_ADDR)
                mem_state inside {WRITE_ADDR, WRITE_DATA};
            else
                mem_state == WRITE_DATA;
        }
    }

    // 4- For a read-only sequence, every Read Address operation shall always be followed by Read Data. 
    //    After a Read Data operation shall always be followed by Read Address. 
    constraint read_c {
        if (rst_n && rx_valid) {
            if (prev_state == READ_ADDR)
                mem_state == READ_DATA;
            else
                mem_state == READ_ADDR;
        }
    }

    // 5- For a randomized read/write sequence
    // A. After Write Address There will be followed by either Write Address or Write Data
    // B. After Write Data There will be distribution to be 60% Read Address and 40% Write Address
    // C. After Read Address There will be Read Data
    // D. After Read Data There will be distribution to be 60% Write Address and 40% Read Address
    constraint write_read_c {
        if (rst_n && rx_valid) {
            if (prev_state == WRITE_ADDR)
              mem_state inside {WRITE_ADDR, WRITE_DATA};
            else if (prev_state == WRITE_DATA)
              mem_state dist {READ_ADDR :/ 60, WRITE_ADDR :/ 40};
            else if (prev_state == READ_ADDR)
              mem_state == READ_DATA;
            else if (prev_state == READ_DATA)
              mem_state dist {WRITE_ADDR :/ 60, READ_ADDR :/ 40};
            else
              mem_state inside {WRITE_ADDR, READ_ADDR};
        }
    }

    constraint din_c {din[9:8] == mem_state;}

    function void post_randomize();
        if (rst_n && rx_valid)
            prev_state = mem_state;
    endfunction
endclass
endpackage