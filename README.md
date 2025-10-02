# Fixed-width N-bit integers

## Overview

Implement template class `fwnbi::basic_integer<size_t Bits, class DigitT, bool Signed>`
with semantic as fundamental integer types.

Valid values of `Bits`: $2^n$, where $n > 0$ and $\text{Bits} \ge \text{bits in DigitT}$.  
Valid values of `DigitT`: `uint8_t`, `uint16_t`, `uint32_t`
(and `uint64_t` if available type `__uint128_t`, GCC extension).

## Namespace `fwnbi`

### Class `basic_integer<...>`

**Types:**  
`digit_type` - equal template parameter `DigitT`  
`double_digit_type` - type with width twice as wide as `digit_type`

**Static constants:**  
`bit_width` - equal template parameter `Bits`  
`digit_width` - bit width of `digit_type`  
`digit_count` - count of digits in `basic_integer<...>`  
`is_signed` - equal template parameter `Signed`

**Static functions:**  
`max()` - return max value for current `basic_integer<...>`  
`min()` - return min value for current `basic_integer<...>`

**Constructors:**  
`basic_integer()` - default constructor (set all zero)  
`basic_integer(digit_type)` - create integer from one digit  
`basic_integer(digit_type (&)[digit_count])` - create integer from array of digits

**Conversions:**  
`bool` - `true` if integer is zero, otherwise `false`  
`digit_type` *explicit* - return first digit  
`double_digit_type` *explicit* - return first and second digit  
`basic_integer<!Signed, ...>` - toggle sign of integer  
`basic_integer<BgBits, ...>` - expand bit width, $\text{BgBits} > \text{Bits}$  
`basic_integer<TnBits, ...>` *explicit* - narrow bit width, $\text{TnBits} < \text{Bits}$  
`basic_integer<OtherDigitT, ...>` - change digit type, $\text{OtherDigitT} \ne \text{DigitT}$

**Support methods:**  
`bool sign_bit()` - return value of MSB  
`int sign()` - n > 0 => +1, n = 0 => 0, n < 0 => -1  
`void clear()` - set all digits in zero  
`bool bit(size_t)` - return value of bit by index, $0 \le \text{index} < \text{Bits}$  
`void bit(size_t, bool)` - set bit by index, $0 \le \text{index} < \text{Bits}$  
`uint8_t hex(size_t)` - return value of hex digit by index, $0 \le \text{index} < \frac{\text{Bits}}{4}$  
`void hex(size_t, uint8_t)` - set hex digit by index, $0 \le \text{index} < \frac{\text{Bits}}{4}$  
`void split(basic_integer<Bits/2, ...>&, basic_integer<Bits/2, ...>&)` - split current integer by upper and lower parts  
`void merge(const basic_integer<Bits/2, ...>&, const basic_integer<Bits/2, ...>&)` - merge upper and lower parts to current integer  
`basic_integer<BgBits, ...> expand()` - expand bit width without copy sign bit, $\text{BgBits} > \text{Bits}$  
`bool add_with_carry(const basic_integer<...>&, bool = false)` - add first and second argument to integer and return carry  
`bool add_with_carry(digit_type, bool = false)` - add first and second argument to integer and return carry  
`void swap(basic_integer<...>&)` - swap value of current integer and argument