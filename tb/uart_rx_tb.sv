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
	logic 	[31:0]	baud_cnt;
	logic			baud_tick;
	
	initial begin
	clk = 0;
	rst_ = 1;
	rx_serial = 1;
	baud_cnt = 0;
	restart_uart;
	//edge case function test
	send_data(8'hff);
	send_data(8'h00);
	
	//random case tests
	repeat($urandom_range(5,10)) begin
		send_data($urandom_range(0,255));
	end
	
	restart_uart;
	//bug injection direct test
	bad_start;
	
	repeat(5) @(posedge clk);
	$stop;
	end //initial
	
	always #5 clk = ~clk;
	
	always @(posedge clk) begin
    if (baud_cnt == DIVISOR-1)
        baud_cnt <= 0;
    else
        baud_cnt <= baud_cnt + 1;
	end

	assign baud_tick = (baud_cnt == DIVISOR-1);
	
	//====================//
	//  Task Declarations //
	//====================//
	
	task automatic restart_uart;
		@(negedge clk) rst_ = 1;
		@(negedge clk) rst_ = 0;
		repeat(2) @(negedge clk);
		rst_ = 1;
		rx_serial = 1;
	endtask
	
	task automatic send_data(input logic [7:0] val);
		logic	[9:0]	shifter;
		shifter = {1'b1,val,1'b0}; //{stop,val,start}
		baud_cnt = 0;
		rx_serial = shifter[0];
		shifter = {1'b1,shifter[9:1]};
		repeat(9) @(posedge baud_tick) begin
			rx_serial = shifter[0];
			shifter = {1'b1,shifter[9:1]};
		end
		@(posedge rx_valid or posedge rx_error)
			if(rx_data != val) $error("Scoreboard mismatch! Expected %0d, got %0d", val, rx_data);
		@(posedge baud_tick);
	endtask
	
	task automatic bad_start;
		baud_cnt = 0;
		rx_serial = 0;
		repeat(10) @(negedge clk);
		rx_serial = 1;
		@(posedge baud_tick);
	endtask

endmodule 