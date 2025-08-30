
module uart_fd_tb;

	parameter	CLK_FREQ = 50_000_000;
	parameter	BAUD_RATE = 115200;
	
	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;
	
	logic			clk;
	logic			rst_;
	logic			tx_start;
	logic	[7:0]	tx_data;
	logic			rx_serial;
	wire			tx_serial;
	wire	[7:0]	rx_data;
	wire			rx_valid;
	wire			rx_error;
	wire			tx_busy;
	
	uart_fd #(CLK_FREQ, BAUD_RATE) my_uart(.clk, .rst_, .tx_start, .tx_data, .rx_serial,
		.tx_serial, .rx_data, .rx_valid, .rx_error, .tx_busy);
		
	bind uart_fd uart_fd_sva #(CLK_FREQ, BAUD_RATE) my_uart_bind
		(.clk, .rst_, .tx_start, .tx_data, .rx_serial, .tx_serial, .rx_data, .rx_valid,
			.rx_error, .tx_busy);
	
	
	initial begin
		clk = 0;
		rst_ = 1;
		tx_start = 0;
		tx_data = 0;
		rx_serial = 1;
		
		repeat(2) @(posedge clk);
		$stop;
	end //initial
	
	always #5 clk = ~clk;

endmodule 