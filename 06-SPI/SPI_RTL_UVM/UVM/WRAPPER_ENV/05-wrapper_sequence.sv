package wrapper_sequence_pkg;
import wrapper_seq_item_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

class reset_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(reset_sequence);
    wrapper_seq_item rst_seq_item;

    function new(string name = "reset_sequence");
        super.new(name);
    endfunction 

    task body();
        rst_seq_item = wrapper_seq_item::type_id::create("rst_seq_item");
        start_item(rst_seq_item);
        rst_seq_item.rst_n = 0;
        rst_seq_item.SS_n = 0;
        rst_seq_item.MOSI = 0;
        finish_item(rst_seq_item);
    endtask
endclass 

class write_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(write_sequence);
    wrapper_seq_item write_seq_item;

    function new(string name = "write_sequence");
        super.new(name);
    endfunction 

    task body();
        write_seq_item = wrapper_seq_item::type_id::create("write_seq_item"); 
        repeat(10000) begin
            start_item(write_seq_item);
            assert(write_seq_item.randomize() with {write_seq_item.mode_control == 0;});
            finish_item(write_seq_item);
        end
    endtask
endclass 

class read_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(read_sequence);
    wrapper_seq_item read_seq_item;

    function new(string name = "read_sequence");
        super.new(name);
    endfunction 

    task body();
        read_seq_item = wrapper_seq_item::type_id::create("read_seq_item");
        repeat(10000) begin
            start_item(read_seq_item);
            assert(read_seq_item.randomize() with {read_seq_item.mode_control == 1;});
            finish_item(read_seq_item);
        end
    endtask
endclass 

class write_read_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(write_read_sequence);
    wrapper_seq_item wr_rd_seq_item;

    function new(string name = "write_read_sequence");
        super.new(name);
    endfunction 

    task body();
        wr_rd_seq_item = wrapper_seq_item::type_id::create("wr_rd_seq_item");
        repeat(10000) begin
            start_item(wr_rd_seq_item);
            assert(wr_rd_seq_item.randomize() with {wr_rd_seq_item.mode_control == 2;});
            finish_item(wr_rd_seq_item);
        end
    endtask
endclass 
endpackage


// Another Sequence Solution Corresponding to the Another Sequence Item

/*
package wrapper_sequence_pkg;
import wrapper_seq_item_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

class reset_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(reset_sequence);
    wrapper_seq_item rst_seq_item;

    function new(string name = "reset_sequence");
        super.new(name);
    endfunction 

    task body();
        rst_seq_item = wrapper_seq_item::type_id::create("rst_seq_item");
        start_item(rst_seq_item);
        rst_seq_item.rst_n = 0;
        rst_seq_item.SS_n = 0;
        rst_seq_item.MOSI = 0;
        finish_item(rst_seq_item);
    endtask
endclass 

class write_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(write_sequence);
    wrapper_seq_item write_seq_item;

    function new(string name = "write_sequence");
        super.new(name);
    endfunction 

    task body();
        write_seq_item = wrapper_seq_item::type_id::create("write_seq_item"); 
        repeat(10000) begin
            write_seq_item.write_c.constraint_mode(1);
            write_seq_item.read_c.constraint_mode(0);
            write_seq_item.write_read_c.constraint_mode(0);
            start_item(write_seq_item);
            assert(write_seq_item.randomize());
            finish_item(write_seq_item);
        end
    endtask
endclass 

class read_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(read_sequence);
    wrapper_seq_item read_seq_item;

    function new(string name = "read_sequence");
        super.new(name);
    endfunction 

    task body();
        read_seq_item = wrapper_seq_item::type_id::create("read_seq_item");
        repeat(10000) begin
            read_seq_item.write_c.constraint_mode(0);
            read_seq_item.read_c.constraint_mode(1);
            read_seq_item.write_read_c.constraint_mode(0);
            start_item(read_seq_item);
            assert(read_seq_item.randomize());
            finish_item(read_seq_item);
        end
    endtask
endclass 

class write_read_sequence extends uvm_sequence #(wrapper_seq_item);
    `uvm_object_utils(write_read_sequence);
    wrapper_seq_item wr_rd_seq_item;

    function new(string name = "write_read_sequence");
        super.new(name);
    endfunction 

    task body();
        wr_rd_seq_item = wrapper_seq_item::type_id::create("wr_rd_seq_item");
        repeat(10000) begin
            wr_rd_seq_item.write_c.constraint_mode(0);
            wr_rd_seq_item.read_c.constraint_mode(0);
            wr_rd_seq_item.write_read_c.constraint_mode(1);
            start_item(wr_rd_seq_item);
            assert(wr_rd_seq_item.randomize());
            finish_item(wr_rd_seq_item);
        end
    endtask
endclass 
endpackage
*/
