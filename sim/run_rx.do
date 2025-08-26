# ================================
# UART_RX Simulation Run Script (run.do)
# Run from the sim/ directory
# ================================

# Clean and recreate work directory
vdel -all
vlib work

# Compile RTL, assertions, and testbench
vlog -sv ../rtl/uart_rx.sv
vlog -sv ../tb/uart_rx_tb.sv
vlog -sv ../assertions/uart_rx_sva.sv


# Run simulation (with limited optimization for waveform viewing)
vsim -voptargs=+acc work.uart_rx_tb 

# Record sim log
transcript file sim_output.log

# Plot waveform
add wave -r uart_rx_tb/*

# Run until completion
run -all

#quit -sim
