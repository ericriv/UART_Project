`define	baud_tick my_uart.baud_tick

module uart_tx_tb; 
	parameter	CLK_FREQ = 50_000_000;
	parameter	BAUD_RATE = 115200;
	
	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;


	logic			clk;
	logic			rst_;
	logic			tx_start;
	logic	[7:0]	tx_data;
	wire			tx_serial;
	wire			tx_busy;

	uart_tx #(CLK_FREQ, BAUD_RATE) my_uart(.clk, .rst_, .tx_start, .tx_data, .tx_serial, .tx_busy);

	bind uart_tx uart_tx_sva #(CLK_FREQ, BAUD_RATE) my_uart_bind
	(.clk, .rst_, .tx_start, .tx_data, .tx_serial, .tx_busy);

	logic ref_q[$];
	

	initial begin
	clk = 0;
	rst_ = 1;
	tx_start = 0;
	tx_data = 0;
	
	//reset and basic direct tests
	reset_uart;
	start_uart(8'hFF);
	start_uart(8'h00);
	reset_uart;
	
	//random input tests
	repeat($urandom_range(10,50)) begin
		start_uart($urandom_range(0,255));
	end
	
	//bug injection tests
	start_uart_start_bug(8'h31);
	repeat(5) @(posedge clk);
	$stop;
	end //initial

	//always @(posedge clk) $display($stime,,,"clk=%b, rst_=%b, tx_start=%b, tx_data=%b, tx_serial=%b, tx_busy=%b", clk, rst_,
	//tx_start, tx_data, tx_serial, tx_busy);

	always #5 clk = ~clk;


	//====================//
	//  Task Declarations //
	//====================//

	task automatic reset_uart;
		@(negedge clk)
		rst_ = 1;
		tx_start = 0;
		tx_data = 0;
		@(negedge clk) rst_ = 0;
		repeat(2) @(negedge clk);
		rst_ = 1;
	endtask
	
	task automatic start_uart(input logic [7:0] val);
		logic expected;
		@(negedge clk);
		tx_data = val;
		tx_start = 1;
		ref_q.push_front(1);
		foreach(val[i]) begin
			ref_q.push_front(val[i]);
		end
		ref_q.push_front(0);
		repeat(2)@(negedge clk)
		tx_start = 0;
		for(int i = 0; i < 9; i++) begin
			@(posedge `baud_tick)
			expected = ref_q.pop_front;
			if(tx_serial != expected) $error("Scoreboard mismatch! Expected %0d, got %0d", expected, tx_serial);
		end
		@(negedge tx_busy);
	endtask
	
	task automatic start_uart_start_bug(input logic [7:0] val);
		logic expected;
		@(negedge clk);
		tx_data = val;
		tx_start = 1;
		ref_q.push_front(1);
		foreach(val[i]) begin
			ref_q.push_front(val[i]);
		end
		ref_q.push_front(0);
		repeat(2)@(negedge clk)
		tx_start = 0;
		for(int i = 0; i < 9; i++) begin
			@(posedge `baud_tick)
			expected = ref_q.pop_front;
			if(tx_serial != expected) $error("Scoreboard mismatch! Expected %0d, got %0d", expected, tx_serial);
			if(i == 5) begin
				@(negedge clk);
				tx_start = 1;
				repeat(2) @(negedge clk);
				tx_start = 0;
			end
		end
		@(negedge tx_busy);
	endtask


endmodule 