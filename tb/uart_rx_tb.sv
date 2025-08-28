`define sample_tick my_uart.sample_tick

module uart_rx_tb;

	parameter	CLK_FREQ = 50_000_000;
	parameter	BAUD_RATE = 115200;
	
	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;
	
	logic			clk;
	logic			rst_;
	logic			rx_serial;
	wire	[7:0]	rx_data;
	wire			rx_valid;
	wire			rx_error;
	
	uart_rx #(CLK_FREQ, BAUD_RATE) my_uart(.clk, .rst_, .rx_serial, .rx_data, .rx_valid, .rx_error);
	
	bind uart_rx uart_rx_sva #(CLK_FREQ, BAUD_RATE) my_uart_bind
	(.clk, .rst_, .rx_serial, .rx_data, .rx_valid, .rx_error);
	
	logic	[7:0]	ref_q[$];
	
	initial begin
	clk = 0;
	rst_ = 1;
	rx_serial = 0;
	
	
	repeat(5) @(posedge clk);
	$stop;
	end //initial
	
	always #5 clk = ~clk;
	
	//====================//
	//  Task Declarations //
	//====================//

endmodule 