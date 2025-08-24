module uart_tx_tb; 
	parameter	CLK_FREQ = 50_000_000;
	parameter	BAUD_RATE = 115200;


	logic			clk;
	logic			rst_;
	logic			tx_start;
	logic	[7:0]	tx_data;
	wire			tx_serial;
	wire			tx_busy;

	uart_tx #(CLK_FREQ, BAUD_RATE) my_uart(.clk, .rst_, .tx_start, .tx_data, .tx_serial, .tx_busy);

	bind uart_tx uart_tx_sva #(CLK_FREQ, BAUD_RATE) my_uart_bind
	(.clk, .rst_, .tx_start, .tx_data, .tx_serial, .tx_busy);


	initial begin
	clk = 0;
	rst_ = 1;
	tx_start = 0;
	tx_data = 0;
	
	$stop;
	end //initial

	always @(posedge clk) $display($stime,,,"clk=%b, rst_=%b, tx_start=%b, tx_data=%b, tx_serial=%b, tx_busy=%b", clk, rst_,
	tx_start, tx_data, tx_serial, tx_busy);

	always #5 clk = ~clk;


	//====================//
	//  Task Declarations //
	//====================//




endmodule 