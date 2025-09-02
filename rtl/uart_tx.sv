module uart_tx #(
parameter	CLK_FREQ = 50_000_000,
parameter	BAUD_RATE = 115200
)(
input	logic			clk,
input 	logic			rst_,
input	logic			tx_start,
input	logic	[7:0]	tx_data,
output	logic			tx_serial,
output	logic			tx_busy
);

	localparam	int	DIVISOR = CLK_FREQ/BAUD_RATE;
	
	typedef enum logic [1:0] {IDLE, START, DATA, STOP} state_t;
	state_t state;

	logic	[31:0]	baud_cnt;
	logic	[2:0]	bit_index;
	logic	[7:0]	shifter;
	logic			baud_tick;
	
	assign baud_tick = (baud_cnt == DIVISOR-1);

	always_ff @(posedge clk or negedge rst_) begin
		if(!rst_) begin
			state <= IDLE;
			baud_cnt <= 0;
			tx_serial <= 1;
			tx_busy <= 0;
			shifter <= 0;
			bit_index <= 0;
		end //rst_
		
		else begin
			case(state)
			
			IDLE: begin
				tx_serial <= 1;
				tx_busy <= 0;
				baud_cnt <= 0;
				if(tx_start) begin
					state <= START;
					tx_busy <= 1;
					shifter <= tx_data;
				end //tx_start
			end //IDLE
			
			START: begin
				tx_serial <= 0;	//drive low to START
				if(baud_tick) begin
					state <= DATA;
					bit_index <= 0;
					baud_cnt <= 0;
				end else
					baud_cnt <= baud_cnt + 1;
			end //START
			
			DATA: begin
				tx_serial <= shifter[0];
				if(baud_tick) begin
					baud_cnt <= 0;
					shifter <= {1'b0, shifter[7:1]};
					if(bit_index == 3'b111)
						state <= STOP;
					else
						bit_index <= bit_index + 1;
				end else
					baud_cnt = baud_cnt + 1;
			end //DATA
			
			STOP: begin
				tx_serial <= 1; //drive high to end
				state <= IDLE;
				baud_cnt <= 0;
				tx_busy <= 0;
			end //STOP
			
			endcase
		end //normal function
		
	end //always
endmodule 