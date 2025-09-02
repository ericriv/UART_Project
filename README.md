# UART_Project
Implementation and verification of a Universal Asynchronous Receiver/Transmitter (UART) in three progressive stages.  
This project demonstrates RTL design skills and SystemVerilog/UVM verification practices.  


## Block Diagrams
- **UART TX**: Parallel-to-serial shift register with start/stop framing.
- **UART RX**: Serial-to-parallel with oversampling and start/stop detection.
- **Full Duplex UART**: Combined TX/RX with shared baud generator.  

(Diagrams located in `docs/` folder)

## DUTs
- **UART Transmitter (TX-only)**
  - Parameterizable baud rate (via divisor input)
  - Parallel data input, serial output (`tx_serial`)
  - Ports: `clk, rst_, tx_start, tx_data, tx_serial, tx_busy`

- **UART Receiver (RX-only)**
  - Oversampling (configurable rate, default 16x baud)
  - Start-bit detection and mid-bit sampling
  - Error detection: framing error (invalid stop bit)
  - Ports: `clk, rst_, rx_serial, rx_data, rx_valid, rx_error`

- **Full Duplex UART**
  - Integrated TX and RX with shared baud generator
  - Supports simultaneous transmission and reception
  - Ports: `clk, rst_, tx_start, tx_data, tx_serial, tx_busy, rx_serial, rx_data, rx_valid, rx_error`


## Verification Objectives
- Verify correct reset behavior
- Verify functional correctness of TX serialization
- Verify RX start-bit detection, oversampling, and data recovery
- Verify corner cases (back-to-back transfers, underflow/overflow, framing errors)
- Verify full-duplex operation (TX and RX simultaneous)


## Verification Methodology
- **SystemVerilog Assertions (SVA)**  
  - Check start/stop bits
  - Check baud timing
  - Check RX framing error detection
- **UVM Testbench**  
  - Transaction class for UART frames
  - Driver (stimulates DUT TX/RX)
  - Monitor (observes `tx_serial`, reconstructs bits)
  - Scoreboard (compares expected vs observed data)
  - Environment + test sequences
- **Functional Coverage**  
  - Data byte coverage (0x00–0xFF)
  - Start/stop/parity coverage (if parity extension added)
  - Corner-case conditions


## Testbench Strategy
- **Directed Tests**
  - Single-byte TX transmit
  - RX mid-bit sampling correctness
  - Error injection (bad stop bit)
  - Back-to-back byte transfers
- **Randomized Tests**
  - Random UART frames over long streams
  - Random TX and RX overlap (full duplex stress test)
  
## Status
- [x] UART TX RTL + directed testbench
- [x] UART RX RTL + directed testbench
- [x] UART Full Duplex RTL + directed testbench 
- [ ] UVM testbench
- [x] Randomized testing + coverage collection
- [ ] Quartus custom IP core


## Future Work
- Add parity support (even/odd or hamming weight)
- Add configurable data length (7/8/9 bits)
- Add integration test with loopback mode (TX → RX directly)