module uart_rx #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input 	logic			rst_,
input	logic			rx_serial,
output	logic	[7:0]	rx_data,
output	logic			rx_valid,
output	logic			rx_error
);
	
	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;
	
	typedef enum {IDLE, START, DATA, STOP} state_t;
	state_t state;
	
	logic 	[31:0]	baud_cnt;
	logic	[2:0]	bit_index;
	logic	[7:0]	shifter;
	logic			sample_tick;
	
	always_ff @(posedge clk or negedge rst_) begin
		
		if(!rst_) begin
			state <= IDLE;
			rx_data <= 0;
			rx_valid <= 0;
			rx_error <= 0;
			baud_cnt <= 0;
			bit_index <= 0;
			shifter <= 0;
		end
		
		else begin
			case(state)
				IDLE: begin
					rx_valid <= 0;
					rx_error <= 0;
					baud_cnt <= 0;
					bit_index <= 0;
					shifter <= 0;
					if(!rx_serial)
						state <= START;
				end
				
				START: begin
					if(baud_cnt == DIVISOR/2) begin
						if(!rx_serial)
							state <= DATA;
						else 
							state <= IDLE;
						baud_cnt <= 0;
					end else
						baud_cnt <= baud_cnt + 1;
				end
				
				DATA: begin
					if(baud_cnt == DIVISOR-1) begin
						baud_cnt <= 0;
						shifter <= {rx_serial,shifter[7:1]};
						if(bit_index == 3'b111)
							state <= STOP;
						else
							bit_index <= bit_index + 1;
					end else
						baud_cnt <= baud_cnt + 1;
				end
				
				STOP: begin
					if(baud_cnt == DIVISOR-1) begin
						if(rx_serial) begin
							rx_data <= shifter;
							rx_valid <= 1;
						end else
							rx_error <= 1;
						state <= IDLE;
					end else
						baud_cnt <= baud_cnt + 1;
				end
			endcase
		end
	
	end 


endmodule