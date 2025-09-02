`define	baud_tick_tx my_uart.my_uart_tx.baud_tick


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
			
	logic 			ref_q[$];
	logic 	[31:0]	baud_cnt;
	logic			baud_tick_rx;
	logic 			rx_serial_drv;
	logic			loopback_en;
	
	initial begin
		clk = 0;
		rst_ = 1;
		tx_start = 0;
		tx_data = 0;
		rx_serial_drv = 1;
		loopback_en = 0;
		
		reset_uart;
		
		//seperate normal edgecase tests
		start_uart_tx(8'hff);
		start_uart_rx(8'hff);
		start_uart_tx(8'h00);
		start_uart_rx(8'h00);
		
		//simultanious normal tests
		fork begin
			start_uart_tx(8'hff);
		end begin
			start_uart_rx(8'hff);
		end join
		
		fork begin
			start_uart_tx(8'h00);
		end begin
			start_uart_rx(8'h00);
		end join
		
		//directed tests
		reset_uart;
		fork begin
			bad_start_rx;
		end begin
			bad_start_tx(8'hff);
		end join
		bad_stop_rx;
		
		//scoreboard driven loop random testing
		loopback_en = 1;
		reset_uart;
		repeat($urandom_range(10,50)) begin
			start_loop($urandom_range(0,255));
		end
		
		repeat(2) @(posedge clk);
		$stop;
	end //initial
	
	always #5 clk = ~clk;
	
	always @(posedge clk) begin
    if (baud_cnt == DIVISOR-1)
        baud_cnt <= 0;
    else
        baud_cnt <= baud_cnt + 1;
	end

	assign baud_tick_rx = (baud_cnt == DIVISOR-1);
	
	assign rx_serial = (loopback_en) ? tx_serial : rx_serial_drv;
	
	//====================//
	//  Task Declarations //
	//====================//

	task automatic reset_uart;
		@(negedge clk)
		rst_ = 1;
		tx_start = 0;
		tx_data = 0;
		rx_serial_drv = 1;
		@(negedge clk) rst_ = 0;
		repeat(2) @(negedge clk);
		rst_ = 1;
	endtask
	
	task automatic start_loop(input logic [7:0] val);
		@(negedge clk);
		tx_data = val;
		  tx_start = 1;
		  @(negedge clk) 
		  tx_start = 0;
		  @(posedge rx_valid or posedge rx_error);
			if(rx_error)
				$error("rx error occured");
			else if (rx_data != val)
				$error("Loopback mismatch! Expected %0h, got %0h", val, rx_data);
		@(negedge clk);
	endtask
	
	task automatic start_uart_tx(input logic [7:0] val);
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
			@(posedge `baud_tick_tx)
			expected = ref_q.pop_front;
			if(tx_serial != expected) $error("Scoreboard mismatch tx! Expected %0d, got %0d", expected, tx_serial);
		end
		@(negedge tx_busy);
	endtask
	
	task automatic bad_start_tx(input logic [7:0] val);
		logic expected;
		@(negedge clk);
		tx_data = val;
		tx_start = 1;
		ref_q.push_front(1);
		foreach(val[i]) begin
			ref_q.push_front(val[i]);
		end
		ref_q.push_front(0);
		repeat(2)@(negedge clk);
		tx_start = 0;
		for(int i = 0; i < 9; i++) begin
			@(posedge `baud_tick_tx)
			expected = ref_q.pop_front;
			if(tx_serial != expected) $error("Scoreboard mismatch tx! Expected %0d, got %0d", expected, tx_serial);
			if(i == 5) begin
				@(negedge clk);
				tx_start = 1;
				repeat(2) @(negedge clk);
				tx_start = 0;
			end
		end
		@(negedge tx_busy);
	endtask
	
	task automatic start_uart_rx(input logic [7:0] val);
		logic	[9:0]	shifter;
		shifter = {1'b1,val,1'b0}; //{stop,val,start}
		baud_cnt = 0;
		rx_serial_drv = shifter[0];
		shifter = {1'b1,shifter[9:1]};
		repeat(9) @(posedge baud_tick_rx) begin
			rx_serial_drv = shifter[0];
			shifter = {1'b1,shifter[9:1]};
		end
		@(posedge rx_valid or posedge rx_error)
			if(rx_data != val) $error("Scoreboard mismatch rx! Expected %0d, got %0d. rx_error = %b", val, rx_data, rx_error);
		@(posedge baud_tick_rx);
	endtask
	
	
	task automatic bad_stop_rx;
		logic	[9:0]	shifter;
		shifter = {1'b0,8'hff,1'b0}; //{bad_stop,val,start}
		baud_cnt = 0;
		rx_serial_drv = shifter[0];
		shifter = {1'b1,shifter[9:1]};
		repeat(9) @(posedge baud_tick_rx) begin
			rx_serial_drv = shifter[0];
			shifter = {1'b1,shifter[9:1]};
		end
		repeat(2) @(posedge baud_tick_rx);
	endtask
	
	task automatic bad_start_rx;
		baud_cnt = 0;
		rx_serial_drv = 0;
		repeat(10) @(negedge clk);
		rx_serial_drv = 1;
		@(posedge baud_tick_rx);
	endtask

endmodule 