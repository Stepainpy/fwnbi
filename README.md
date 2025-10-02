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

