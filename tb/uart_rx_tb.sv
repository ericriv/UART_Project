

module uart_rx_tbl

	parameter	CLK_FREQ = 50_000_000;
	parameter	BAUD_RATE = 115200;
	
	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;
	
	input	logic			clk;
	input 	logic			rst_;
	input	logic			rx_serial;
	wire			[7:0]	rx_data;
	wire					rx_valid;
	wire					rx_error;

endmodule 