
module uart_tx_tb;
	logic clk;
	int divisor;
	initial clk = 0;
	always #5 clk = ~clk;

	uart_tx_if uif(clk);

	uart_tx #(.CLK_FREQ(50_000_000), .BAUD_RATE(115200)) my_uart(
		.clk(clk),
		.rst_(uif.rst_),
		.tx_start(uif.tx_start),
		.tx_data(uif.tx_data),
		.tx_serial(uif.tx_serial),
		.tx_busy(uif.tx_busy)
	);
  
  /*
	initial begin
		uif.rst_ = 0;
		repeat(5) @(posedge clk);
		uif.rst_ = 1;
	end
  */

	initial begin
		divisor = my_uart.CLK_FREQ / my_uart.BAUD_RATE;
		uvm_config_db#(virtual uart_tx_if)::set(null, "*", "vif", uif);
		uvm_config_db#(int)::set(null, "*", "baud_divisor", divisor);
		run_test("uart_tx_test");
	end
endmodule