import adder_package::*;
module simpleadder_oop_tb ();
	// declare your interface here
	adder_if adderif();

	// instantiate DUT and connect it to interface
	simpleadder DUT (
		.clk(adderif.clk),
		.en_i(adderif.en_i),
		.ina(adderif.ina),
		.inb(adderif.inb),
		.en_o(adderif.en_o),
		.out(adderif.out)
	);
	bind simpleadder adder_sva sva_inst (adderif.en_i, adderif.ina, adderif.inb, adderif.clk, adderif.out, adderif.en_o, DUT.temp_out);

	// declare components handle
	adder_generator m_generator;
	adder_driver    m_driver;
	monitor_output  m_monitor_output;
	monitor_input   m_monitor_input;
	adder_collector m_cov_collector;
	adder_checker   m_adder_checker;

	// construct all object
	// connect virtual interface handles
	function void build_env ();
		m_generator      = new();
		m_driver         = new(adderif);
		m_monitor_input  = new(adderif);
		m_monitor_output = new(adderif);
		m_cov_collector  = new();
		m_adder_checker  = new(); // no interface should be used here
	endfunction
	
	// connect mailboxes in object to each other
	// remember that mailboxes are classes that can be accessed via object handles 
	function void connect_env (); // Connect mailboxes
		m_driver.stimulus_mbx   = m_generator.stimulus_mbx;
		
		m_adder_checker.in_mbx  = m_monitor_input.in_check_mbx;
		m_adder_checker.out_mbx = m_monitor_output.out_check_mbx;

		m_cov_collector.in_mbx  = m_monitor_input.in_cov_mbx;
		m_cov_collector.out_mbx = m_monitor_output.out_cov_mbx;
	endfunction
	
	initial begin
		$display("--------- Start  Testing ---------");
		build_env();
		connect_env();
		// fork join_any the main tasks inside your classes here
		fork : test_fork
			m_generator.run(TESTS);
			m_driver.run();
			m_monitor_input.run();
			m_monitor_output.run();
			m_adder_checker.run();
			m_cov_collector.run();
			wait(m_adder_checker.done) disable test_fork;
		join
		$finish();
	end

	// final block 
	final begin // It operates after $finish
		$display("\n========= Final Report =========");
		$display("Correct Count : %0d", m_adder_checker.correct_count);
		$display("Error Count   : %0d", m_adder_checker.error_count);
		$display("Total Tests   : %0d", TESTS);
		$display("================================\n");
	end
endmodule