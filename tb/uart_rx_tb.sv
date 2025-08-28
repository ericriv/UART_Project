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
	rx_serial = 0;
	baud_cnt = 0;
	restart_uart;
	send_data($urandom_range(0,255));
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
	endtask
	
	task automatic send_data(input logic [7:0] val);
		logic	[9:0]	shifter;
		shifter = {1'b1,val,1'b0}; //{stop,val,start}
		baud_cnt = 0;
		foreach(shifter[i]) begin
			rx_serial = shifter[i];
			@(posedge baud_tick);
		end
		@(posedge clk iff rx_valid)
			if(rx_data != val) $error("Scoreboard mismatch! Expected %0d, got %0d", val, rx_data);
	endtask

endmodule 