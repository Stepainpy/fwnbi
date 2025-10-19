# Fixed-width N-bit integers

## Overview

Implement template class `fwnbi::basic_integer<size_t Bits, class DigitT, bool Signed>`
with semantic as fundamental integer types.

Valid values of `Bits`: $\text{Bits} > 0$ and
$\text{Bits} \equiv 0 \pmod{\text{bits in DigitT}}$.  
Valid values of `DigitT`: `fwnbi::digit::u8`, `fwnbi::digit::u16`, `fwnbi::digit::u32`
(and `fwnbi::digit::u64` if available type `__uint128_t`, GCC extension).

For multiplication use, the Karatsuba algorithm.

## Namespace `fwnbi`

### Class `basic_integer<size_t Bits, class DigitT, bool Signed>`

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
`basic_integer(const digit_type (&)[digit_count])` - create integer from array of digits  
`basic_integer(const std::array<digit_type, digit_count>&)` - create integer from std::array of digits

**Conversions:**  
`bool` - `false` if integer is zero, otherwise `true`  
`digit_type` - return first digit  
`double_digit_type` - return first and second digit  
`basic_integer<!Signed, ...>` - toggle sign of integer  
`basic_integer<BgBits, ...>` - expand bit width, $\text{BgBits} > \text{Bits}$  
`basic_integer<TnBits, ...>` - narrow bit width, $\text{TnBits} < \text{Bits}$  
`basic_integer<OtherDigitT, ...>` - change digit type, $\text{OtherDigitT} \ne \text{DigitT}$

**Comparison:**  
`int compare(const basic_integer<...>&)` - 3-way comparison  
`std::strong_ordering operator<=>(const basic_integer<...>&)` *since C++20* - standard 3-way comparison

**Support methods:**  
`bool sign_bit()` - return value of MSB  
`int sign()` - n > 0 => +1, n = 0 => 0, n < 0 => -1  
`size_t width()` - return actual bit width of current value  
`void clear()` - set all digits in zero  
`bool bit(size_t)` - return value of bit by index, $0 \le \text{index} < \text{Bits}$  
`void bit(size_t, bool)` - set bit by index, $0 \le \text{index} < \text{Bits}$  
`uint8_t hex(size_t)` - return value of hex digit by index, $0 \le \text{index} < \frac{\text{Bits}}{4}$  
`void hex(size_t, uint8_t)` - set hex digit by index, $0 \le \text{index} < \frac{\text{Bits}}{4}$  
`void split(basic_integer<BitsU, ...>&, basic_integer<BitsL, ...>&)` - split current integer by upper and lower parts  
`void merge(const basic_integer<BitsU, ...>&, const basic_integer<BitsL, ...>&)` - merge upper and lower parts to current integer  
`basic_integer<BgBits, ...> expand()` - expand bit width without copy sign bit, $\text{BgBits} > \text{Bits}$  
`bool add_with_carry(const basic_integer<...>&, bool = false)` - add first and second argument to integer and return carry  
`bool add_with_carry(digit_type, bool = false)` - add first and second argument to integer and return carry  
`void swap(basic_integer<...>&)` - swap value of current integer and argument

**Additional operators:**  
`digit_type& operator[](size_t)` - return digit by index  
`<<`, `>>`, `<<=`, `>>=` - if count is negative turn left/right to right/left

### Functions

`fullmul` - return 2N-bit result of multiplication N-bit integers  
`abs` - return absolute value of integer  
`rotl`/`rotr` - bit rotation, if count is negative turn left/right to right/left  
`clz` - return count `0`-bit from MSB to before first `1`-bit  
`ctz` - return count `0`-bit from LSB to before first `1`-bit  
`popcount` - return count of `1`-bit in integer  
`sqr` - return square of integer with twice width  
`isqrt` - return `floor(sqrt(x))` of integer  
`gcd` - return greate common divisor  
`lcm` - return least common multiplier

### Default provided type aliases

`uintN_t<Bits, DigitT = fwnbi::digit::u32>`/`intN_t<Bits, DigitT = fwnbi::digit::u32>` - aliases with preset signedness  
`uint128_t`/`uint256_t`/`uint512_t`/`uint1024_t` - unsigned aliases  
`int128_t`/`int256_t`/`int512_t`/`int1024_t` - signed aliases

## Namespace `fwnbi::digit`

`u8`/`u16`/`u32`/`u64` - digit types

## Namespace `fwnbi::literals`

`_ull128`/`_ull256`/`_ull512`/`_ull1024` - unsigned  
`_ll128`/`_ll256`/`_ll512`/`_ll1024` - signed

## Namespace `std`

`void swap(...)` - swapping to integers  
`struct numeric_limits` - information about `basic_integer<...>`  
`struct is_integral` - return `true`  
`struct is_unsigned`/`struct is_signed` - answer by question  
`struct make_unsigned`/`struct make_signed` - return type  
`struct hash` - calculate function FNVa-64 for bytes in integer  
`std::string to_string(...)` - convert integer to `std::string`  
`... strtoll(...)` - convert C-string to signed integer  
`... strtoull(...)` - convert C-string to unsigned integer  
`... operator<<(...)` - output to `std::basic_ostream<...>`  
`... operator>>(...)` - input from `std::basic_istream<...>`  
`... to_chars(...)` *since C++17* - fast convert to string  
`... from_chars(...)` *since C++17* - fast convert from string  
`struct formatter<...>` *since C++20* - helper class for format library