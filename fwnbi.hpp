/* Fixed-width N-bit integers
 *   Implement 'class basic_integer' with
 *   semantic as fundamental integer types.
 *
 * Algorithm links:
 *   rotate array - https://stackoverflow.com/a/31175162
 *   to string    - https://stackoverflow.com/a/8023937
 *   division     - https://en.wikipedia.org/wiki/Division_algorithm
 *   modpow       - https://en.wikipedia.org/wiki/Modular_exponentiation
 *   square       - https://ido.tsu.ru/iop_res1/teorcrypto/text/1_3.html
 *   gcd          - https://ido.tsu.ru/iop_res1/teorcrypto/text/1_26.html
 */

#ifndef FIXED_WIDTH_N_BITS_INTEGERS_HPP
#define FIXED_WIDTH_N_BITS_INTEGERS_HPP

#if __cplusplus < 201103L
#  error This code require C++11
#endif

#include <cstddef>
#include <cstdint>
#include <climits>

#if __cpp_impl_three_way_comparison >= 201907L
#  include <compare>
#endif

#ifdef _MSC_VER
#  include <intrin.h>
#  include <stdlib.h>
#endif

#if __cplusplus >= 201402L
#  define FWNBI_CONSTEXPR14 constexpr
#else
#  define FWNBI_CONSTEXPR14
#endif

#if __cplusplus >= 201703L
#  define FWNBI_CONSTEXPR17 constexpr
#else
#  define FWNBI_CONSTEXPR17
#endif

#if __cplusplus >= 202002L
#  define FWNBI_CONSTEXPR20 constexpr
#else
#  define FWNBI_CONSTEXPR20
#endif

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
#  define FWNBI_ENABLE_UINT128_TYPE 1
#else
#  define FWNBI_ENABLE_UINT128_TYPE 0
#endif

namespace std { template <class T, size_t N> struct array; }

namespace fwnbi {

namespace detail {

template <bool B, class T, class F> struct conditional { using type = F; };
template <class T, class F> struct conditional<true, T, F> { using type = T; };

template <bool B, class T> struct enable_if {};
template <class T> struct enable_if<true, T> { using type = T; };

template <bool B, class T, class F>
using conditional_t = typename conditional<B, T, F>::type;
template <bool B, class T>
using enable_if_t = typename enable_if<B, T>::type;

using u8  = conditional_t<UINT8_MAX  == UINT_FAST8_MAX , uint_fast8_t , uint8_t >;
using u16 = conditional_t<UINT16_MAX == UINT_FAST16_MAX, uint_fast16_t, uint16_t>;
using u32 = conditional_t<UINT32_MAX == UINT_FAST32_MAX, uint_fast32_t, uint32_t>;
using u64 = conditional_t<UINT64_MAX == UINT_FAST64_MAX, uint_fast64_t, uint64_t>;

template <class T> struct make_double_digit {};
template <> struct make_double_digit<u8 > { using type = u16; };
template <> struct make_double_digit<u16> { using type = u32; };
template <> struct make_double_digit<u32> { using type = u64; };
template <> struct make_double_digit<u64> {
#if FWNBI_ENABLE_UINT128_TYPE
    using type = __uint128_t;
#endif
};

template <class T>
using make_double_digit_t = typename make_double_digit<T>::type;

template <size_t B> struct biggest_digit {
    using type = conditional_t<
        FWNBI_ENABLE_UINT128_TYPE &&
        B % 64 == 0, u64, conditional_t<
        B % 32 == 0, u32, conditional_t<
        B % 16 == 0, u16, u8>>>;
};
template <size_t B> using biggest_digit_t = typename biggest_digit<B>::type;

template <size_t V> struct size_s { static constexpr size_t value = V; };
template <class  T> struct bitsof {
    static constexpr size_t value = sizeof(T) * CHAR_BIT;
    using type = size_s<value>;
};

template <class T>
FWNBI_CONSTEXPR14 void reverse(T* first, T* last) noexcept {
    for (--last; first < last; ++first, --last) {
        T t = *first; *first = *last; *last = t;
    }
}

template <class T>
FWNBI_CONSTEXPR14 T* copy(const T* first, size_t count, T* out) noexcept {
    for (size_t i = 0; i < count; ++i) *out++ = *first++;
    return out;
}

#ifdef __GNUC__
constexpr size_t popcount(u64 n) noexcept { return __builtin_popcountll(n); }
#else
FWNBI_CONSTEXPR14 size_t popcount(u64 n) noexcept {
    constexpr u64 m1  = 0x5555555555555555ull;
    constexpr u64 m2  = 0x3333333333333333ull;
    constexpr u64 m4  = 0x0F0F0F0F0F0F0F0Full;
    constexpr u64 h01 = 0x0101010101010101ull;
    n -= (n >> 1) & m1;
    n = (n & m2) + ((n >> 2) & m2);
    n = (n + (n >> 4)) & m4;
    return (n * h01) >> 56;
}
#endif

#if defined(__GNUC__)
constexpr size_t ctz(u64 n) noexcept { return __builtin_ctzll(n); }

template <class T>
constexpr size_t clz(T n) noexcept {
    return n ? __builtin_clzll(n) - bitsof<unsigned long long>::value
        + bitsof<T>::value : bitsof<T>::value;
}

constexpr u8  bswap(u8  n) noexcept { return n; }
constexpr u16 bswap(u16 n) noexcept { return __builtin_bswap16(n); }
constexpr u32 bswap(u32 n) noexcept { return __builtin_bswap32(n); }
constexpr u64 bswap(u64 n) noexcept { return __builtin_bswap64(n); }
#elif defined(_MSC_VER)
FWNBI_CONSTEXPR14 size_t ctz(u64 n) noexcept
    { unsigned long out = 0; return _BitScanForward64(&out, n) ? out : 64; }

template <class T>
FWNBI_CONSTEXPR14 size_t clz(T n) noexcept {
    unsigned long out = 0; return _BitScanReverse64(&out, n)
        ? bitsof<T>::value - 1 - out : bitsof<T>::value;
}

FWNBI_CONSTEXPR14 u8  bswap(u8  n) noexcept { return n; }
FWNBI_CONSTEXPR14 u16 bswap(u16 n) noexcept { return _byteswap_ushort(n); }
FWNBI_CONSTEXPR14 u32 bswap(u32 n) noexcept { return _byteswap_ulong (n); }
FWNBI_CONSTEXPR14 u64 bswap(u64 n) noexcept { return _byteswap_uint64(n); }
#else
FWNBI_CONSTEXPR14 size_t ctz(u64 n) noexcept {
    size_t out = 0;
    if (!n) return 64;
    for (; (n & 1) == 0; n >>= 1) ++out;
    return out;
}

template <class T>
FWNBI_CONSTEXPR14 size_t clz(T n) noexcept {
    constexpr T mask = T(1) << (bitsof<T>::value - 1);
    size_t out = 0;
    if (!n) return bitsof<T>::value;
    for (; (n & mask) == 0; n <<= 1) ++out;
    return out;
}

constexpr u8  bswap(u8  n) noexcept { return n; }
constexpr u16 bswap(u16 n) noexcept {
    return (n & UINT16_C(0xFF00)) >> 8
        |  (n & UINT16_C(0x00FF)) << 8;
}
constexpr u32 bswap(u32 n) noexcept {
    return (n & UINT32_C(0xFF000000)) >> 24
        |  (n & UINT32_C(0x00FF0000)) >>  8
        |  (n & UINT32_C(0x0000FF00)) <<  8
        |  (n & UINT32_C(0x000000FF)) << 24;
}
constexpr u64 bswap(u64 n) noexcept {
    return (n & UINT64_C(0xFF00000000000000)) >> 56
        |  (n & UINT64_C(0x00FF000000000000)) >> 40
        |  (n & UINT64_C(0x0000FF0000000000)) >> 24
        |  (n & UINT64_C(0x000000FF00000000)) >>  8
        |  (n & UINT64_C(0x00000000FF000000)) <<  8
        |  (n & UINT64_C(0x0000000000FF0000)) << 24
        |  (n & UINT64_C(0x000000000000FF00)) << 40
        |  (n & UINT64_C(0x00000000000000FF)) << 56;
}
#endif

} // namespace detail

template <size_t Bits, class DigitT, bool Signed>
class basic_integer {
    static_assert(
        Bits > 0 && Bits % detail::bitsof<DigitT>::value == 0,
        "Bits is not a multiple of digit width"
    );

public:
    using        digit_type = DigitT;
    using double_digit_type = detail::make_double_digit_t<DigitT>;

    using       reference =       digit_type&;
    using const_reference = const digit_type&;
    using       iterator  =       digit_type*;
    using const_iterator  = const digit_type*;

public:
    static constexpr size_t   bit_width = Bits;
    static constexpr size_t digit_width = detail::bitsof<DigitT>::value;
    static constexpr size_t digit_count = bit_width / digit_width;
    static constexpr bool     is_signed = Signed;

public:
    FWNBI_CONSTEXPR14 basic_integer() noexcept : digits() {}
    FWNBI_CONSTEXPR14 basic_integer(const basic_integer& ) noexcept = default;
    FWNBI_CONSTEXPR14 basic_integer(      basic_integer&&) noexcept = default;
    FWNBI_CONSTEXPR14 basic_integer& operator=(const basic_integer& ) noexcept = default;
    FWNBI_CONSTEXPR14 basic_integer& operator=(      basic_integer&&) noexcept = default;

    FWNBI_CONSTEXPR14 basic_integer(digit_type digit) noexcept : digits() { digits[0] = digit; }
    FWNBI_CONSTEXPR14 basic_integer(double_digit_type dbl_digit) noexcept : digits() {
        digits[0] = static_cast<digit_type>(dbl_digit);
        if FWNBI_CONSTEXPR17 (digit_count > 1)
            digits[1] = static_cast<digit_type>(dbl_digit >> digit_width);
    }
    FWNBI_CONSTEXPR14 basic_integer(const digit_type (&in_digits)[digit_count]) noexcept
        : digits() { detail::copy(in_digits, digit_count, digits); }
    FWNBI_CONSTEXPR14 basic_integer(const std::array<digit_type, digit_count>& in_digits) noexcept;

    FWNBI_CONSTEXPR20 ~basic_integer() noexcept = default;

public:
    static FWNBI_CONSTEXPR14 basic_integer max() noexcept
        { return ~basic_integer<Bits, DigitT, false>() >> size_t(is_signed); }
    static FWNBI_CONSTEXPR14 basic_integer min() noexcept
        { return max() + digit_type(1); }

public:
    FWNBI_CONSTEXPR14 operator bool() const noexcept {
        for (auto digit : digits)
            if (digit) return true;
        return false;
    }

    FWNBI_CONSTEXPR14 operator digit_type() const noexcept { return digits[0]; }

    FWNBI_CONSTEXPR14 operator double_digit_type() const noexcept {
        double_digit_type out = digits[0];
        if FWNBI_CONSTEXPR17 (digit_count > 1)
            out |= double_digit_type(digits[1]) << digit_width;
        return out;
    }

    FWNBI_CONSTEXPR14 operator basic_integer<Bits, DigitT, !Signed>() const noexcept {
        return basic_integer<Bits, DigitT, !Signed>(digits);
    }

    template <size_t BgBits, bool S, detail::enable_if_t<(BgBits > Bits), int> = 0>
    FWNBI_CONSTEXPR14 operator basic_integer<BgBits, DigitT, S>() const noexcept {
        basic_integer<BgBits, DigitT, S> out;
        if (sign() < 0) out = ~out;
        detail::copy(digits, digit_count, out.digits);
        return out;
    }

    template <size_t TnBits, bool S, detail::enable_if_t<(TnBits < Bits), int> = 0>
    FWNBI_CONSTEXPR14 operator basic_integer<TnBits, DigitT, S>() const noexcept {
        basic_integer<TnBits, DigitT, S> out;
        detail::copy(digits, out.digit_count, out.digits);
        return out;
    }

    template <class BgDigitT, bool S,
        detail::enable_if_t<(sizeof(BgDigitT) > sizeof(DigitT)), int> = 0>
    FWNBI_CONSTEXPR14 operator basic_integer<Bits, BgDigitT, S>() const noexcept {
        const size_t ratio = sizeof(BgDigitT) / sizeof(DigitT);
        basic_integer<Bits, BgDigitT, S> out;
        for (size_t i = 0; i < out.digit_count; i++)
            for (size_t j = ratio; j --> 0;) {
                out.digits[i] <<= digit_width;
                out.digits[i] |= static_cast<BgDigitT>(digits[i * ratio + j]);
            }
        return out;
    }

    template <class TnDigitT, bool S,
        detail::enable_if_t<(sizeof(TnDigitT) < sizeof(DigitT)), int> = 0>
    FWNBI_CONSTEXPR14 operator basic_integer<Bits, TnDigitT, S>() const noexcept {
        const size_t ratio = sizeof(DigitT) / sizeof(TnDigitT);
        basic_integer<Bits, TnDigitT, S> out;
        for (size_t i = 0; i < digit_count; i++)
            for (size_t j = 0; j < ratio; j++)
                out.digits[i * ratio + j] = static_cast<TnDigitT>(
                    digits[i] >> (j * out.digit_width)
                );
        return out;
    }

public:
    FWNBI_CONSTEXPR14 bool sign_bit() const noexcept {
        return digits[digit_count - 1] >> (digit_width - 1);
    }

    FWNBI_CONSTEXPR14 int sign() const noexcept {
        if (is_signed && sign_bit()) return -1;
        return static_cast<bool>(*this);
    }

    FWNBI_CONSTEXPR14 size_t width() const noexcept {
        for (size_t i = digit_count; i --> 0;)
            if (digits[i])
                return (i + 1) * digit_width - detail::clz(digits[i]);
        return 0;
    }

    FWNBI_CONSTEXPR14 void clear() noexcept {
        for (auto& digit : digits) digit = digit_type(0);
    }

    FWNBI_CONSTEXPR14 bool bit(size_t index) const noexcept {
        if (index >= bit_width) return false;
        return digits[index / digit_width] >> (index % digit_width) & 1;
    }

    FWNBI_CONSTEXPR14 void bit(size_t index, bool value) noexcept {
        if (index >= bit_width) return;
        const size_t d_i = index / digit_width;
        const size_t b_i = index % digit_width;
        const digit_type mask = ~(digit_type(1) << b_i);
        (digits[d_i] &= mask) |= digit_type(value) << b_i;
    }

    FWNBI_CONSTEXPR14 uint8_t hex(size_t index) const noexcept {
        if (index >= bit_width / 4) return 0;
        return digits[index * 4 / digit_width] >> (index * 4 % digit_width) & 15;
    }

    FWNBI_CONSTEXPR14 void hex(size_t index, uint8_t value) noexcept {
        if (index >= bit_width / 4) return;
        const size_t d_i = index * 4 / digit_width;
        const size_t h_i = index * 4 % digit_width;
        const digit_type mask = ~(digit_type(15) << h_i);
        (digits[d_i] &= mask) |= digit_type(value & 15) << h_i;
    }

    template <size_t BitsU, size_t BitsL>
    FWNBI_CONSTEXPR14 auto split(
        basic_integer<BitsU, DigitT, Signed>& upper,
        basic_integer<BitsL, DigitT, Signed>& lower
    ) const noexcept -> detail::enable_if_t<BitsU + BitsL == Bits, void> {
        detail::copy(digits                    , lower.digit_count, lower.digits);
        detail::copy(digits + lower.digit_count, upper.digit_count, upper.digits);
    }

    template <size_t BitsU, size_t BitsL>
    FWNBI_CONSTEXPR14 auto merge(
        const basic_integer<BitsU, DigitT, Signed>& upper,
        const basic_integer<BitsL, DigitT, Signed>& lower
    ) noexcept -> detail::enable_if_t<BitsU + BitsL == Bits, void> {
        digit_type* middle =
        detail::copy(lower.digits, lower.digit_count, digits);
        detail::copy(upper.digits, upper.digit_count, middle);
    }

    template <size_t BgBits, detail::enable_if_t<(BgBits > Bits), int> = 0>
    FWNBI_CONSTEXPR14 basic_integer<BgBits, DigitT, Signed> expand() const noexcept {
        basic_integer<BgBits, DigitT, Signed> out;
        detail::copy(digits, digit_count, out.digits);
        return out;
    }

    FWNBI_CONSTEXPR14 bool add_with_carry(const basic_integer& rhs, bool carry = false) noexcept {
        for (size_t i = 0; i < digit_count; i++) {
            digit_type prev = digits[i];
            digits[i] += rhs.digits[i] + carry;
            carry = carry ? prev >= digits[i] : prev > digits[i];
        }
        return carry;
    }

    FWNBI_CONSTEXPR14 bool add_with_carry(digit_type rhs, bool carry = false) noexcept {
        digit_type prev = digits[0];
        digits[0] += rhs + carry;
        carry = carry ? prev >= digits[0] : prev > digits[0];
        for (size_t i = 1; carry && i < digit_count; i++) {
            prev = digits[i]; carry = prev > ++digits[i];
        }
        return carry;
    }

    FWNBI_CONSTEXPR14 void swap(basic_integer& rhs) noexcept {
        for (size_t i = 0; i < digit_count; i++) {
            digit_type t = digits[i];
            digits[i] = rhs.digits[i];
            rhs.digits[i] = t;
        }
    }

public:
    FWNBI_CONSTEXPR14       digit_type* data()       noexcept { return digits; }
    FWNBI_CONSTEXPR14 const digit_type* data() const noexcept { return digits; }

    FWNBI_CONSTEXPR14       iterator  begin()       noexcept { return digits; }
    FWNBI_CONSTEXPR14 const_iterator  begin() const noexcept { return digits; }
    FWNBI_CONSTEXPR14 const_iterator cbegin() const noexcept { return digits; }

    FWNBI_CONSTEXPR14       iterator  end()       noexcept { return digits + digit_count; }
    FWNBI_CONSTEXPR14 const_iterator  end() const noexcept { return digits + digit_count; }
    FWNBI_CONSTEXPR14 const_iterator cend() const noexcept { return digits + digit_count; }

private:
    FWNBI_CONSTEXPR14 void small_shift_left(size_t shift) noexcept {
        if (!shift || shift >= digit_width) return;
        for (size_t i = digit_count; i --> 1;)
            digits[i] = digits[i] << shift | digits[i - 1] >> (digit_width - shift);
        digits[0] <<= shift;
    }

    FWNBI_CONSTEXPR14 void small_shift_right(size_t shift) noexcept {
        if (!shift || shift >= digit_width) return;
        digit_type saved_sign_bit = sign() < 0;
        for (size_t i = 0; i < digit_count - 1; i++)
            digits[i] = digits[i] >> shift | digits[i + 1] << (digit_width - shift);
        digits[digit_count - 1] >>= shift;
        digits[digit_count - 1] |= (-saved_sign_bit) << (digit_width - shift);
    }

    FWNBI_CONSTEXPR14 void digit_shift_left(size_t shift) noexcept {
        if (shift >= digit_count) return clear();
        for (size_t i = digit_count; i --> shift;)
            digits[i] = digits[i - shift];
        for (size_t i = 0; i < shift; i++)
            digits[i] = digit_type(0);
    }

    FWNBI_CONSTEXPR14 void digit_shift_right(size_t shift) noexcept {
        if (shift >= digit_count) return clear();
        digit_type saved_sign_bit = sign() < 0;
        for (size_t i = 0; i < digit_count - shift; i++)
            digits[i] = digits[i + shift];
        for (size_t i = digit_count; i --> digit_count - shift;)
            digits[i] = -saved_sign_bit;
    }

    FWNBI_CONSTEXPR14 void small_rotate_left(size_t shift) noexcept {
        if (!shift || shift >= digit_width) return;
        digit_type part = digits[digit_count - 1] >> (digit_width - shift);
        small_shift_left(shift);
        digits[0] |= part;
    }

    FWNBI_CONSTEXPR14 void small_rotate_right(size_t shift) noexcept {
        if (!shift || shift >= digit_width) return;
        digit_type part = digits[0] << (digit_width - shift);
        small_shift_right(shift);
        digits[digit_count - 1] |= part;
    }

    FWNBI_CONSTEXPR14 void digit_rotate_left(size_t shift) noexcept {
        shift %= digit_count; if (!shift) return;
        detail::reverse(digits, digits + digit_count - shift);
        detail::reverse(digits + digit_count - shift, digits + digit_count);
        detail::reverse(digits, digits + digit_count);
    }

    FWNBI_CONSTEXPR14 void digit_rotate_right(size_t shift) noexcept {
        shift %= digit_count; if (!shift) return;
        detail::reverse(digits, digits + shift);
        detail::reverse(digits + shift, digits + digit_count);
        detail::reverse(digits, digits + digit_count);
    }

    struct divmod_t { basic_integer quot, rem; };

    FWNBI_CONSTEXPR14 divmod_t divmod_unsigned(const basic_integer& divisor) const noexcept {
        divmod_t out {};
        for (size_t i = bit_width; i --> 0;) {
            out.rem.small_shift_left(1);
            out.rem.digits[0] |= digit_type(bit(i));
            if (out.rem >= divisor) {
                out.rem -= divisor;
                out.quot.bit(i, true);
            }
        }
        return out;
    }

    FWNBI_CONSTEXPR14 divmod_t divmod(const basic_integer& divisor) const noexcept {
        if (!divisor) return {basic_integer::max(), basic_integer::max()};
        if (divisor.sign() < 0) {
            divmod_t out = divmod(-divisor);
            return {-out.quot, out.rem};
        }
        if (sign() < 0) {
            const basic_integer dividend = -(*this);
            divmod_t out = dividend.divmod(divisor);
            if (!out.rem) return {-out.quot, basic_integer()};
            else return {--(-out.quot), divisor - out.rem};
        }
        return divmod_unsigned(divisor);
    }

public:
    FWNBI_CONSTEXPR14       reference operator[](size_t index)       noexcept { return digits[index]; }
    FWNBI_CONSTEXPR14 const_reference operator[](size_t index) const noexcept { return digits[index]; }

public:
    FWNBI_CONSTEXPR14 basic_integer operator+() const noexcept { return *this; }

    FWNBI_CONSTEXPR14 basic_integer operator-() const noexcept {
        basic_integer out = ~(*this);
        out.add_with_carry(1);
        return out;
    }

    FWNBI_CONSTEXPR14 basic_integer operator~() const noexcept {
        basic_integer out = *this;
        for (auto& digit : out.digits) digit = ~digit;
        return out;
    }

public:
    FWNBI_CONSTEXPR14 basic_integer& operator++() noexcept
        { add_with_carry(digit_type(1)); return *this; }
    FWNBI_CONSTEXPR14 basic_integer& operator--() noexcept
        { add_with_carry(~basic_integer()); return *this; }
    FWNBI_CONSTEXPR14 basic_integer operator++(int) noexcept
        { basic_integer out = *this; ++(*this); return out; }
    FWNBI_CONSTEXPR14 basic_integer operator--(int) noexcept
        { basic_integer out = *this; --(*this); return out; }

public:
    FWNBI_CONSTEXPR14 basic_integer& operator+=(const basic_integer& rhs) noexcept
        { add_with_carry(rhs); return *this; }
    FWNBI_CONSTEXPR14 basic_integer& operator+=(digit_type rhs) noexcept
        { add_with_carry(rhs); return *this; }
    FWNBI_CONSTEXPR14 basic_integer& operator-=(const basic_integer& rhs) noexcept
        { add_with_carry(-rhs); return *this; }
    FWNBI_CONSTEXPR14 basic_integer& operator-=(digit_type rhs) noexcept
        { add_with_carry(-basic_integer(rhs)); return *this; }

    FWNBI_CONSTEXPR14 basic_integer& operator*=(const basic_integer&) noexcept;
    FWNBI_CONSTEXPR14 basic_integer& operator*=(digit_type rhs) noexcept {
        basic_integer out;
        for (; rhs; rhs >>= 1, *this <<= 1)
            if (rhs & 1) out += *this;
        return *this = out;
    }

    FWNBI_CONSTEXPR14 basic_integer& operator/=(const basic_integer& rhs) noexcept
        { return *this = divmod(rhs).quot; }
    FWNBI_CONSTEXPR14 basic_integer& operator%=(const basic_integer& rhs) noexcept
        { return *this = divmod(rhs).rem;  }
    FWNBI_CONSTEXPR14 basic_integer& operator/=(digit_type rhs) noexcept
        { return *this = divmod(basic_integer(rhs)).quot; }
    FWNBI_CONSTEXPR14 basic_integer& operator%=(digit_type rhs) noexcept
        { return *this = divmod(basic_integer(rhs)).rem;  }

    FWNBI_CONSTEXPR14 basic_integer& operator&=(const basic_integer& rhs) noexcept {
        for (size_t i = 0; i < digit_count; i++)
            digits[i] &= rhs.digits[i];
        return *this;
    }
    FWNBI_CONSTEXPR14 basic_integer& operator|=(const basic_integer& rhs) noexcept {
        for (size_t i = 0; i < digit_count; i++)
            digits[i] |= rhs.digits[i];
        return *this;
    }
    FWNBI_CONSTEXPR14 basic_integer& operator^=(const basic_integer& rhs) noexcept {
        for (size_t i = 0; i < digit_count; i++)
            digits[i] ^= rhs.digits[i];
        return *this;
    }

    FWNBI_CONSTEXPR14 basic_integer& operator<<=(size_t shift) noexcept {
        digit_shift_left(shift / digit_width);
        small_shift_left(shift % digit_width);
        return *this;
    }
    FWNBI_CONSTEXPR14 basic_integer& operator>>=(size_t shift) noexcept {
        digit_shift_right(shift / digit_width);
        small_shift_right(shift % digit_width);
        return *this;
    }

    FWNBI_CONSTEXPR14 basic_integer& operator<<=(int shift) noexcept {
        if (shift > 0) return *this <<= static_cast<size_t>( shift);
        if (shift < 0) return *this >>= static_cast<size_t>(-shift);
        return *this;
    }
    FWNBI_CONSTEXPR14 basic_integer& operator>>=(int shift) noexcept {
        if (shift > 0) return *this >>= static_cast<size_t>( shift);
        if (shift < 0) return *this <<= static_cast<size_t>(-shift);
        return *this;
    }

public:
    FWNBI_CONSTEXPR14 basic_integer operator+(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) += rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator-(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) -= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator*(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) *= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator/(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) /= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator%(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) %= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator&(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) &= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator|(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) |= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator^(const basic_integer& rhs) const noexcept
        { return basic_integer(*this) ^= rhs; }

    FWNBI_CONSTEXPR14 basic_integer operator+(digit_type rhs) const noexcept
        { return basic_integer(*this) += rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator-(digit_type rhs) const noexcept
        { return basic_integer(*this) -= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator*(digit_type rhs) const noexcept
        { return basic_integer(*this) *= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator/(digit_type rhs) const noexcept
        { return basic_integer(*this) /= rhs; }
    FWNBI_CONSTEXPR14 basic_integer operator%(digit_type rhs) const noexcept
        { return basic_integer(*this) %= rhs; }

    FWNBI_CONSTEXPR14 basic_integer operator<<(size_t shift) const noexcept
        { return basic_integer(*this) <<= shift; }
    FWNBI_CONSTEXPR14 basic_integer operator>>(size_t shift) const noexcept
        { return basic_integer(*this) >>= shift; }
    FWNBI_CONSTEXPR14 basic_integer operator<<(int shift) const noexcept
        { return basic_integer(*this) <<= shift; }
    FWNBI_CONSTEXPR14 basic_integer operator>>(int shift) const noexcept
        { return basic_integer(*this) >>= shift; }

public:
    FWNBI_CONSTEXPR14 int compare(const basic_integer& rhs) const noexcept {
        if (!is_signed || sign_bit() == rhs.sign_bit()) {
            size_t i = digit_count - 1;
            while (i && digits[i] == rhs.digits[i]) --i;
            return (digits[i] > rhs.digits[i]) - (digits[i] < rhs.digits[i]);
        }
        return !sign_bit() * 2 - 1;
    }

    FWNBI_CONSTEXPR14 bool operator==(const basic_integer& rhs) const noexcept
        { return compare(rhs) == 0; }
#if __cpp_impl_three_way_comparison >= 201907L
    constexpr std::strong_ordering operator<=>(const basic_integer& rhs) const noexcept {
        const int cmp = compare(rhs);
        if (cmp < 0) return std::strong_ordering::less;
        if (cmp > 0) return std::strong_ordering::greater;
        return std::strong_ordering::equal;
    }
#else
    FWNBI_CONSTEXPR14 bool operator!=(const basic_integer& rhs) const noexcept
        { return compare(rhs) != 0; }
    FWNBI_CONSTEXPR14 bool operator< (const basic_integer& rhs) const noexcept
        { return compare(rhs) <  0; }
    FWNBI_CONSTEXPR14 bool operator> (const basic_integer& rhs) const noexcept
        { return compare(rhs) >  0; }
    FWNBI_CONSTEXPR14 bool operator<=(const basic_integer& rhs) const noexcept
        { return compare(rhs) <= 0; }
    FWNBI_CONSTEXPR14 bool operator>=(const basic_integer& rhs) const noexcept
        { return compare(rhs) >= 0; }
#endif

public:
    template <size_t B, class D> friend FWNBI_CONSTEXPR14 basic_integer<B, D, false>
    rotl(basic_integer<B, D, false> lhs, size_t shift) noexcept;
    template <size_t B, class D> friend FWNBI_CONSTEXPR14 basic_integer<B, D, false>
    rotr(basic_integer<B, D, false> lhs, size_t shift) noexcept;
    template <size_t B, class D> friend FWNBI_CONSTEXPR14 basic_integer<B, D, false>
    rotl(basic_integer<B, D, false> lhs, int shift) noexcept;
    template <size_t B, class D> friend FWNBI_CONSTEXPR14 basic_integer<B, D, false>
    rotr(basic_integer<B, D, false> lhs, int shift) noexcept;
    template <size_t B, class D> friend FWNBI_CONSTEXPR14 basic_integer<B, D, false>
    byteswap(basic_integer<B, D, false> value) noexcept;

private:
    template <size_t B, class D, bool S> friend class basic_integer;

    digit_type digits[digit_count];
}; // class basic_integer

namespace detail {

template <class Bt, class D, bool S>
struct karatsuba {
    static FWNBI_CONSTEXPR14 basic_integer<Bt::value*2, D, S> calc(
        const basic_integer<Bt::value, D, S>& lhs,
        const basic_integer<Bt::value, D, S>& rhs
    ) noexcept {
        constexpr size_t near_p2 =
            size_t(1) << (bitsof<size_t>::value - clz(Bt::value - 1));
        using int2B = basic_integer<near_p2*2, D, false>;

        basic_integer<near_p2  , D, S> x10 = lhs;
        basic_integer<near_p2  , D, S> y10 = rhs;
        basic_integer<near_p2/2, D, S> x0, x1, x2;
        basic_integer<near_p2/2, D, S> y0, y1, y2;
        x10.split(x1, x0); x2 = x1;
        y10.split(y1, y0); y2 = y1;

        bool xc = x2.add_with_carry(x0);
        bool yc = y2.add_with_carry(y0);

        int2B z0 = karatsuba<size_s<near_p2/2>, D, S>::calc(x0, y0).template expand<near_p2*2>();
        int2B z2 = karatsuba<size_s<near_p2/2>, D, S>::calc(x1, y1).template expand<near_p2*2>();
        int2B z3 = karatsuba<size_s<near_p2/2>, D, S>::calc(x2, y2).template expand<near_p2*2>();

        int2B ex2 = x2.template expand<near_p2*2>();
        int2B ey2 = y2.template expand<near_p2*2>();

        if (xc      ) z3 +=     ey2     << near_p2 / 2;
        if (      yc) z3 +=     ex2     << near_p2 / 2;
        if (xc && yc) z3 += int2B(D(1)) << near_p2    ;
        int2B z1 = z3 - z2 - z0;

        return (z2 << near_p2) + (z1 << near_p2 / 2) + z0;
    }
};

template <class D, bool S>
struct karatsuba<typename bitsof<D>::type, D, S> {
    static FWNBI_CONSTEXPR14 basic_integer<bitsof<D>::value*2, D, S> calc(
        const basic_integer<bitsof<D>::value, D, S>& lhs,
        const basic_integer<bitsof<D>::value, D, S>& rhs
    ) noexcept {
        using int2B = basic_integer<bitsof<D>::value*2, D, S>;
        using dbl_dgt_t = typename int2B::double_digit_type;
        int2B out(
            static_cast<dbl_dgt_t>(lhs[0]) *
            static_cast<dbl_dgt_t>(rhs[0])
        );
        return out;
    }
};

FWNBI_CONSTEXPR14 size_t cexpr_strlen(const char* str) noexcept {
    size_t size = 0;
    while (*str++) ++size;
    return size;
}

FWNBI_CONSTEXPR14 size_t cexpr_strchr(const char* str, char ch) noexcept {
    size_t count = 0;
    for (; *str; str++) if (*str == ch) ++count;
    return count;
}

FWNBI_CONSTEXPR14 bool cexpr_isspace(char ch) noexcept {
    return ch ==  ' ' || ch == '\n' || ch == '\t'
        || ch == '\r' || ch == '\v' || ch == '\f';
}

FWNBI_CONSTEXPR14 bool cexpr_isdigit(char ch) noexcept {
    return ch == '0' || ch == '1' || ch == '2'
        || ch == '3' || ch == '4' || ch == '5'
        || ch == '6' || ch == '7' || ch == '8'
        || ch == '9';
}

FWNBI_CONSTEXPR14 size_t prime_log2(unsigned n) noexcept {
    if (!n) return size_t(-1);
    size_t out = 0;
    for (; n > 1; n >>= 1) ++out;
    return out;
}

template <class T>
FWNBI_CONSTEXPR14 T char2digit(char ch) noexcept {
    if ('0' <= ch && ch <= '9')
        return T(     ch - '0');
    if ('a' <= ch && ch <= 'z')
        return T(10 + ch - 'a');
    if ('A' <= ch && ch <= 'Z')
        return T(10 + ch - 'A');
    return T(-1);
}

static constexpr auto log10_2 = 0.3010299956639812L;

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> from_literal(const char* literal) noexcept {
    enum class lit_base {
        bin = 1, oct = 3, dec = 0, hex = 4
    } base = lit_base::dec;

    if (*literal == '0') {
        base = lit_base::oct; ++literal;
        /*  */ if (*literal == 'x' || *literal == 'X') {
            base = lit_base::hex; ++literal;
        } else if (*literal == 'b' || *literal == 'B') {
            base = lit_base::bin; ++literal;
        }
    }

    while (*literal == '0' || *literal == '\'') ++literal;
    const size_t lit_len = cexpr_strlen(literal) - cexpr_strchr(literal, '\'');

    bool goto_exit = false;
    switch (base) {
        case lit_base::bin: goto_exit = lit_len > B  ; break;
        case lit_base::hex: goto_exit = lit_len > B/4; break;
        case lit_base::dec:
            goto_exit = lit_len > static_cast<size_t>(B * log10_2) + 1;
            break;
        case lit_base::oct:
            goto_exit = lit_len > B/3 + 1 ||
                (lit_len == B/3 + 1 && *literal > '3');
            break;
    }
    if (goto_exit)
        return basic_integer<B, D, S>::max();

    basic_integer<B, D, S> out, out_c;
    for (; *literal; ++literal) {
        if (*literal == '\'') continue;
        const D next = char2digit<D>(*literal);
        switch (base) {
            case lit_base::dec: {
                bool carry = false;
                out_c = out << 3;
                carry |= out.bit(B-1) || out.bit(B-2) || out.bit(B-3);
                carry |= out_c.add_with_carry(out << 1);
                carry |= out_c.add_with_carry(next);
                if (carry) return basic_integer<B, D, S>::max();
                out = out_c;
            } break;
            default: {
                out <<= static_cast<size_t>(base);
                out[0] |= next;
            } break;
        }
    }

    return out;
}


static constexpr char digit_alphabet[36] = {
    '0', '1', '2', '3', '4', '5', '6', '7', '8',
    '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h',
    'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q',
    'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'
};

template <size_t B, class D, bool S> FWNBI_CONSTEXPR14 char* to_chars_i(
    char* first, char* last, basic_integer<B, D, S> num, bool* of, int base
) noexcept {
    make_double_digit_t<D> d, r;
    bool is_neg = num.sign() < 0;
    char* pos = first;

    if (is_neg) num = -num;

    do {
        if (pos == last) {
            if (of) *of = true;
            return last;
        }

        r = num[num.digit_count - 1];
        for (size_t i = num.digit_count; i --> 0;) {
            d  = r / base;
            r -= d * base;
            if (i) r = (r << bitsof<D>::value) + num[i - 1];
            num[i] = static_cast<D>(d);
        }

        *pos++ = digit_alphabet[r];
    } while (num);

    if (is_neg) {
        if (pos == last) {
            if (of) *of = true;
            return last;
        } else
            *pos++ = '-';
    }

    reverse(first, pos);
    if (of) *of = false;
    return pos;
}

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 char* to_chars_pow2(
    char* first, char* last, basic_integer<B, D, S> num,
    bool* of, int pow, bool uppercase = false
) noexcept {
    const D mask = (D(1) << pow) - 1;
    char* pos = first;

    do {
        if (pos == last) {
            if (of) *of = true;
            return last;
        }

        D digit = num[0] & mask;
        *pos++ = digit_alphabet[digit]
            - (uppercase && digit >= 10) * 32;
        num >>= pow;
    } while (num);

    reverse(first, pos);
    if (of) *of = false;
    return pos;
}

enum class from_char_res {
    ok, invalid, overflow
};

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> from_chars_i(
    const char* first, const char* last,
    from_char_res& res, const char** end, int base
) noexcept {
    if (end) *end = first;
    res = from_char_res::ok;
    basic_integer<B, D, S> out;
    const char* start = first;

    bool sign = false;
    if (first != last && *first == '-')
        { sign = true; ++first; }
    if (first != last && *first == '+') ++first;

    for (; first != last; first++) {
        const D next = char2digit<D>(*first);
        if (next >= D(base)) break;

        if (!(base & (base - 1))) {
            bool carry = false;
            for (size_t i = 1; i <= prime_log2(base); i++)
                carry |= out.bit(B - i);
            if (carry) {
                res = from_char_res::overflow;
                if (end) *end = last;
                break;
            }
            out <<= prime_log2(base);
            out[0] |= next;
        } else {
            bool prev_sign = out.sign_bit();
            basic_integer<B, D, S> prev = out;
            out *= D(base);
            if (prev > out || prev_sign != out.sign_bit()) {
                res = from_char_res::overflow;
                if (end) *end = last;
                break;
            }
            out += next;
        }
    }

    if (res == from_char_res::overflow)
        for (; first != last; first++)
            if (char2digit<D>(*first) >= D(base))
                break;

    if (start == first || first[-1] == '+' || first[-1] == '-')
        res = from_char_res::invalid;
    if (end) *end = first;

    return sign ? -out : out;
}

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> strto_base(
    const char* str, char** end, int base) noexcept {
    if (!str || base < 0 || base == 1 || base > 36) return {};

    while (cexpr_isspace(*str)) ++str;
    if ((base == 0 || base == 8 || base == 16) && *str == '0') {
        ++str; int new_base = base;
        if (base == 0) new_base = 8;
        if ((base == 0 || base == 16) && *str == 'x')
            { ++str; if (base == 0) new_base = 16; }
        base = new_base;
    }
    if (base == 0) base = 10;

    from_char_res res = from_char_res::ok;
    basic_integer<B, D, S> out = from_chars_i<B, D, S>(
        str, str + cexpr_strlen(str), res,
        const_cast<const char**>(end), base
    );

    switch (res) {
        case from_char_res::ok: return out;
        case from_char_res::overflow:
            return out.sign() < 0
                ? basic_integer<B, D, S>::min()
                : basic_integer<B, D, S>::max();
        case from_char_res::invalid: return {};
    }
}

template <class Bt, class D> struct clz_t {
    static FWNBI_CONSTEXPR14 size_t calc(const basic_integer<Bt::value, D, false>& value) noexcept {
        using intB = basic_integer<Bt::value, D, false>;
        constexpr size_t upper_width = intB::digit_count / 2;
        constexpr size_t lower_width = intB::digit_count - upper_width;
        basic_integer<upper_width * intB::digit_width, D, false> upper;
        basic_integer<lower_width * intB::digit_width, D, false> lower;
        value.split(upper, lower);
        return upper           ? clz_t<size_s<upper.bit_width>, D>::calc(upper)
            :  upper.bit_width + clz_t<size_s<lower.bit_width>, D>::calc(lower);
    }
};

template <class D> struct clz_t<typename bitsof<D>::type, D> {
    static FWNBI_CONSTEXPR14 size_t calc(
        const basic_integer<bitsof<D>::value, D, false>& value
    ) noexcept {
        if (!value[0]) return bitsof<D>::value;
        return clz(value[0]);
    }
};

template <class Bt, class D> struct ctz_t {
    static FWNBI_CONSTEXPR14 size_t calc(const basic_integer<Bt::value, D, false>& value) noexcept {
        using intB = basic_integer<Bt::value, D, false>;
        constexpr size_t upper_width = intB::digit_count / 2;
        constexpr size_t lower_width = intB::digit_count - upper_width;
        basic_integer<upper_width * intB::digit_width, D, false> upper;
        basic_integer<lower_width * intB::digit_width, D, false> lower;
        value.split(upper, lower);
        return lower           ? ctz_t<size_s<lower.bit_width>, D>::calc(lower)
            :  lower.bit_width + ctz_t<size_s<upper.bit_width>, D>::calc(upper);
    }
};

template <class D> struct ctz_t<typename bitsof<D>::type, D> {
    static FWNBI_CONSTEXPR14 size_t calc(
        const basic_integer<bitsof<D>::value, D, false>& value
    ) noexcept {
        if (!value[0]) return bitsof<D>::value;
        return ctz(value[0]);
    }
};

template <class W, class DW>
class uiwc {
public:
    FWNBI_CONSTEXPR14 uiwc(DW w = 0, DW b = 0): word(w), msb(b) {}

    FWNBI_CONSTEXPR14 DW   carry() const noexcept { return msb; }
    FWNBI_CONSTEXPR14 void carry(DW b)   noexcept { msb   =  b; }
    FWNBI_CONSTEXPR14 void dword(DW w)   noexcept { word  =  w; }

    FWNBI_CONSTEXPR14 W lower() const noexcept
        { return static_cast<W>(word); }
    FWNBI_CONSTEXPR14 W upper() const noexcept
        { return static_cast<W>(word >> bitsof<W>::value); }

    FWNBI_CONSTEXPR14 uiwc cr_up() const noexcept {
        return uiwc(word >> bitsof<W>::value | msb << bitsof<W>::value);
    };

    FWNBI_CONSTEXPR14 uiwc twice() const noexcept {
        return uiwc(word << 1, word >> (bitsof<DW>::value - 1));
    }

    FWNBI_CONSTEXPR14 uiwc operator+(const uiwc& rhs) const noexcept {
        return uiwc(word + rhs.word, msb ^ rhs.msb ^ (word > word + rhs.word));
    }

private:
    DW word, msb;
};

} // namespace detail

template <size_t B, class D, bool S> FWNBI_CONSTEXPR14 basic_integer<B, D, S>&
basic_integer<B, D, S>::operator*=(const basic_integer<B, D, S>& rhs) noexcept {
    return *this = detail::karatsuba<detail::size_s<B>, D, S>::calc(*this, rhs);
}

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> operator+(
    D lhs, const basic_integer<B, D, S>& rhs
) noexcept { return rhs + lhs; }
template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> operator*(
    D lhs, const basic_integer<B, D, S>& rhs
) noexcept { return rhs * lhs; }

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B*2, D, S> fullmul(
    const basic_integer<B, D, S>& lhs, const basic_integer<B, D, S>& rhs
) noexcept { return detail::karatsuba<detail::size_s<B>, D, S>::calc(lhs, rhs); }

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S> abs(basic_integer<B, D, S> value) noexcept {
    if (value.sign() < 0) value = -value;
    return value;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> rotl(
    basic_integer<B, D, false> lhs, size_t shift
) noexcept { shift %= B;
    lhs.digit_rotate_left(shift / lhs.digit_width);
    lhs.small_rotate_left(shift % lhs.digit_width);
    return lhs;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> rotr(
    basic_integer<B, D, false> lhs, size_t shift
) noexcept { shift %= B;
    lhs.digit_rotate_right(shift / lhs.digit_width);
    lhs.small_rotate_right(shift % lhs.digit_width);
    return lhs;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> rotl(
    basic_integer<B, D, false> lhs, int shift
) noexcept {
    if (shift > 0) return rotl(lhs, static_cast<size_t>( shift));
    if (shift < 0) return rotr(lhs, static_cast<size_t>(-shift));
    return lhs;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> rotr(
    basic_integer<B, D, false> lhs, int shift
) noexcept {
    if (shift > 0) return rotr(lhs, static_cast<size_t>( shift));
    if (shift < 0) return rotl(lhs, static_cast<size_t>(-shift));
    return lhs;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 size_t clz(const basic_integer<B, D, false>& value) noexcept {
    return detail::clz_t<detail::size_s<B>, D>::calc(value);
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 size_t ctz(const basic_integer<B, D, false>& value) noexcept {
    return detail::ctz_t<detail::size_s<B>, D>::calc(value);
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 size_t popcount(const basic_integer<B, D, false>& value) noexcept {
    size_t out = 0;
    for (auto digit : value)
        out += detail::popcount(digit);
    return out;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> byteswap(
    basic_integer<B, D, false> value
) noexcept {
    for (auto& digit : value) digit = detail::bswap(digit);
    detail::reverse(value.digits, value.digits + value.digit_count);
    return value;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> modpow(
    const basic_integer<B, D, false>& base,
    const basic_integer<B, D, false>& exponent,
    const basic_integer<B, D, false>& modulo
) noexcept {
    basic_integer<B  , D, false> r = D(1);
    basic_integer<B  , D, false> b = base % modulo, e = exponent;
    basic_integer<B*2, D, false> m = modulo;
    for (; e; e >>= 1) {
        if (e[0] % 2)
            r = fullmul(r, b) % m;
        b = fullmul(b, b) % m;
    }
    return r;
}

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B*2, D, S>
sqr(const basic_integer<B, D, S>& value) noexcept {
    using DD = detail::make_double_digit_t<D>;
    using uiwc_t = detail::uiwc<D, DD>;
    basic_integer<B*2, D, S> out; uiwc_t cuv;
    basic_integer<B, D, S> val = abs(value);

    for (size_t i = 0; i < val.digit_count; i++) {
        cuv.dword(DD(out[i*2]) + DD(val[i]) * DD(val[i]));
        cuv.carry(0);
        out[i*2] = cuv.lower();

        for (size_t j = i + 1; j < val.digit_count; j++) {
            cuv = cuv.cr_up() + uiwc_t(out[i + j])
                + uiwc_t(DD(val[i]) * DD(val[j])).twice();
            out[i + j] = cuv.lower();
        }

        auto cu = basic_integer<B*2, D, S>(cuv.upper());
        cu[1] = static_cast<D>(cuv.carry());
        cu <<= (i + val.digit_count) * detail::bitsof<D>::value;
        out += cu;
    }

    return out;
}

template <size_t B, class D> FWNBI_CONSTEXPR14 basic_integer<B, D, false>
isqrt(const basic_integer<B, D, false>& value) noexcept {
    auto out = basic_integer<B, D, false>(1) << ((value.width() + 1) >> 1);
    while (true) {
        auto newout = (out + value / out) >> 1;
        if (newout >= out) return out;
        out = newout;
    }
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B, D, false> gcd(
    const basic_integer<B, D, false>& lhs,
    const basic_integer<B, D, false>& rhs
) noexcept {
    if (!lhs || !rhs) return {};
    basic_integer<B, D, false> a = lhs, b = rhs, c;
    size_t i = ctz(a), j = ctz(b), k = i < j ? i : j;
    a >>= i; b >>= j;
    while (a != b) {
        if (a < b) a.swap(b);
        c = a - b;
        a = c >> ctz(c);
    }
    return a << k;
}

template <size_t B, class D>
FWNBI_CONSTEXPR14 basic_integer<B*2, D, false> lcm(
    const basic_integer<B, D, false>& lhs,
    const basic_integer<B, D, false>& rhs
) noexcept {
    const basic_integer<B, D, false> gcd_res = gcd(lhs, rhs);
    if (!gcd_res) return {};
    return fullmull(lhs / gcd_res, rhs);
}

template <size_t Bits, class DigitT = detail::biggest_digit_t<Bits>>
using uintN_t = basic_integer<Bits, DigitT, false>;
template <size_t Bits, class DigitT = detail::biggest_digit_t<Bits>>
using  intN_t = basic_integer<Bits, DigitT,  true>;

using uint128_t  = uintN_t< 128>;
using uint256_t  = uintN_t< 256>;
using uint512_t  = uintN_t< 512>;
using uint1024_t = uintN_t<1024>;

using  int128_t  =  intN_t< 128>;
using  int256_t  =  intN_t< 256>;
using  int512_t  =  intN_t< 512>;
using  int1024_t =  intN_t<1024>;

#define FWNBI_UINT128_MAX  (::fwnbi::uint128_t ::max())
#define FWNBI_UINT256_MAX  (::fwnbi::uint256_t ::max())
#define FWNBI_UINT512_MAX  (::fwnbi::uint512_t ::max())
#define FWNBI_UINT1024_MAX (::fwnbi::uint1024_t::max())

#define FWNBI_INT128_MIN  (::fwnbi::int128_t ::min())
#define FWNBI_INT256_MIN  (::fwnbi::int256_t ::min())
#define FWNBI_INT512_MIN  (::fwnbi::int512_t ::min())
#define FWNBI_INT1024_MIN (::fwnbi::int1024_t::min())

#define FWNBI_INT128_MAX  (::fwnbi::int128_t ::max())
#define FWNBI_INT256_MAX  (::fwnbi::int256_t ::max())
#define FWNBI_INT512_MAX  (::fwnbi::int512_t ::max())
#define FWNBI_INT1024_MAX (::fwnbi::int1024_t::max())

namespace digit {

using detail::u8;
using detail::u16;
using detail::u32;
using detail::u64;

} // namespace digit

namespace literals {

FWNBI_CONSTEXPR14 uint128_t operator""_ull128(const char* literal) noexcept
    { return detail::from_literal< 128, detail::biggest_digit_t< 128>, false>(literal); }
FWNBI_CONSTEXPR14 uint256_t operator""_ull256(const char* literal) noexcept
    { return detail::from_literal< 256, detail::biggest_digit_t< 256>, false>(literal); }
FWNBI_CONSTEXPR14 uint512_t operator""_ull512(const char* literal) noexcept
    { return detail::from_literal< 512, detail::biggest_digit_t< 512>, false>(literal); }
FWNBI_CONSTEXPR14 uint1024_t operator""_ull1024(const char* literal) noexcept
    { return detail::from_literal<1024, detail::biggest_digit_t<1024>, false>(literal); }

FWNBI_CONSTEXPR14 int128_t operator""_ll128(const char* literal) noexcept
    { return detail::from_literal< 128, detail::biggest_digit_t< 128>, true>(literal); }
FWNBI_CONSTEXPR14 int256_t operator""_ll256(const char* literal) noexcept
    { return detail::from_literal< 256, detail::biggest_digit_t< 256>, true>(literal); }
FWNBI_CONSTEXPR14 int512_t operator""_ll512(const char* literal) noexcept
    { return detail::from_literal< 512, detail::biggest_digit_t< 512>, true>(literal); }
FWNBI_CONSTEXPR14 int1024_t operator""_ll1024(const char* literal) noexcept
    { return detail::from_literal<1024, detail::biggest_digit_t<1024>, true>(literal); }

FWNBI_CONSTEXPR14 basic_integer< 128, detail::u8, false> operator""_ull128d8(const char* literal) noexcept
    { return detail::from_literal< 128, detail::u8, false>(literal); }
FWNBI_CONSTEXPR14 basic_integer< 256, detail::u8, false> operator""_ull256d8(const char* literal) noexcept
    { return detail::from_literal< 256, detail::u8, false>(literal); }
FWNBI_CONSTEXPR14 basic_integer< 512, detail::u8, false> operator""_ull512d8(const char* literal) noexcept
    { return detail::from_literal< 512, detail::u8, false>(literal); }
FWNBI_CONSTEXPR14 basic_integer<1024, detail::u8, false> operator""_ull1024d8(const char* literal) noexcept
    { return detail::from_literal<1024, detail::u8, false>(literal); }

FWNBI_CONSTEXPR14 basic_integer< 128, detail::u8, true> operator""_ll128d8(const char* literal) noexcept
    { return detail::from_literal< 128, detail::u8, true>(literal); }
FWNBI_CONSTEXPR14 basic_integer< 256, detail::u8, true> operator""_ll256d8(const char* literal) noexcept
    { return detail::from_literal< 256, detail::u8, true>(literal); }
FWNBI_CONSTEXPR14 basic_integer< 512, detail::u8, true> operator""_ll512d8(const char* literal) noexcept
    { return detail::from_literal< 512, detail::u8, true>(literal); }
FWNBI_CONSTEXPR14 basic_integer<1024, detail::u8, true> operator""_ll1024d8(const char* literal) noexcept
    { return detail::from_literal<1024, detail::u8, true>(literal); }

#define FWNBI_UINT128_C(literal)  literal ## _ull128
#define FWNBI_UINT256_C(literal)  literal ## _ull256
#define FWNBI_UINT512_C(literal)  literal ## _ull512
#define FWNBI_UINT1024_C(literal) literal ## _ull1024

#define FWNBI_INT128_C(literal)  literal ## _ll128
#define FWNBI_INT256_C(literal)  literal ## _ll256
#define FWNBI_INT512_C(literal)  literal ## _ll512
#define FWNBI_INT1024_C(literal) literal ## _ll1024

} // namespace literals

} // namespace fwnbi

#include <type_traits>
#include <ostream>
#include <istream>
#include <utility>
#include <limits>
#include <string>
#include <array>

#if __cplusplus >= 201703L
#  include <charconv>
#endif

#if __cplusplus >= 202002L
#  include <format>
#endif

namespace fwnbi {

template <size_t B, class D, bool S>
FWNBI_CONSTEXPR14 basic_integer<B, D, S>::basic_integer(
    const std::array<digit_type, digit_count>& in_digits
) noexcept : digits() {
    detail::copy(&in_digits.at(0), digit_count, digits);
}

} // namespace fwnbi

namespace std {

template <size_t B, class D, bool S> void swap(
    fwnbi::basic_integer<B, D, S>& a, fwnbi::basic_integer<B, D, S>& b
) noexcept { a.swap(b); }

template <size_t B, class D, bool S>
struct numeric_limits<fwnbi::basic_integer<B, D, S>> : numeric_limits<D> {
    static constexpr bool is_signed = S;
    static constexpr int digits = B;
    static constexpr int digits10 = static_cast<int>(B * fwnbi::detail::log10_2);

    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S> min() noexcept
        { return fwnbi::basic_integer<B, D, S>::min(); }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S> max() noexcept
        { return fwnbi::basic_integer<B, D, S>::max(); }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S> lowest() noexcept
        { return fwnbi::basic_integer<B, D, S>::min(); }

    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S>       epsilon() noexcept { return {}; }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S>   round_error() noexcept { return {}; }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S>      infinity() noexcept { return {}; }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S>     quite_NaN() noexcept { return {}; }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S> signaling_NaN() noexcept { return {}; }
    static FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, S>    denorm_min() noexcept { return {}; }
};

template <size_t B, class D, bool S>
struct is_integral<fwnbi::basic_integer<B, D, S>> : true_type {};

template <size_t B, class D>
struct is_signed<fwnbi::basic_integer<B, D, false>> : false_type {};
template <size_t B, class D>
struct is_signed<fwnbi::basic_integer<B, D, true>> : true_type {};

template <size_t B, class D>
struct is_unsigned<fwnbi::basic_integer<B, D, false>> : true_type {};
template <size_t B, class D>
struct is_unsigned<fwnbi::basic_integer<B, D, true>> : false_type {};

template <size_t B, class D, bool S>
struct make_signed<fwnbi::basic_integer<B, D, S>> {
    using type = fwnbi::basic_integer<B, D, true>;
};
template <size_t B, class D, bool S>
struct make_unsigned<fwnbi::basic_integer<B, D, S>> {
    using type = fwnbi::basic_integer<B, D, false>;
};

template <size_t B, class D, bool S>
struct hash<fwnbi::basic_integer<B, D, S>> {
    size_t operator()(const fwnbi::basic_integer<B, D, S>& n) const noexcept {
        auto data = reinterpret_cast<const uint8_t*>(&n[0]);
        size_t h = size_t(0xcbf29ce484222325);
        for (size_t i = 0; i < n.digit_count * sizeof(D); i++)
            h = (h * size_t(0x100000001b3)) ^ data[i];
        return h;
    }
};

template <size_t B, class D, bool S>
string to_string(const fwnbi::basic_integer<B, D, S>& value) {
    char buffer[numeric_limits<fwnbi::basic_integer<B, D, S>>::digits10 + 2] {};
    const char* end = fwnbi::detail::to_chars_i(
        buffer, buffer + sizeof buffer, value, nullptr, 10);
    return string(buffer, end - buffer);
}

template <size_t B, class D = fwnbi::detail::biggest_digit_t<B>>
FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, true> strtoll(
    const char* str, char** str_end, int base) noexcept {
    return fwnbi::detail::strto_base<B, D, true>(str, str_end, base);
}

template <size_t B, class D = fwnbi::detail::biggest_digit_t<B>>
FWNBI_CONSTEXPR14 fwnbi::basic_integer<B, D, false> strtoull(
    const char* str, char** str_end, int base) noexcept {
    return fwnbi::detail::strto_base<B, D, false>(str, str_end, base);
}

template <class CharT, class Traits, size_t B, class D, bool S>
basic_ostream<CharT, Traits>& operator<<(
    basic_ostream<CharT, Traits>& os, const fwnbi::basic_integer<B, D, S>& value
) {
    const auto flags = os.flags();
    char buffer[B / 3 + 1 + 2 + 1] {};
    char* buf_end; size_t pos = 0;

    if (value.sign() >= 0 && flags & os.dec && flags & os.showpos)
        buffer[pos++] = '+';

    if (flags & os.showbase) {
        if (flags & (os.hex | os.oct))
            buffer[pos++] = '0';
        if (flags & os.hex)
            buffer[pos++] = 'x';
    }

    /**/ if (flags & os.hex)
        buf_end = fwnbi::detail::to_chars_pow2(
            buffer + pos, buffer + sizeof buffer, value, nullptr,  4);
    else if (flags & os.oct)
        buf_end = fwnbi::detail::to_chars_pow2(
            buffer + pos, buffer + sizeof buffer, value, nullptr,  3);
    else /* os.dec */
        buf_end = fwnbi::detail::to_chars_i(
            buffer + pos, buffer + sizeof buffer, value, nullptr, 10);

    const ptrdiff_t nl = buf_end - buffer;
    const streamsize w = os.width(0);
    const ptrdiff_t lw = w > nl ? w - nl : 0;
    const CharT fillch = os.fill();

    CharT out_buffer[sizeof buffer] {};
    for (size_t i = 0; i < sizeof buffer; i++) {
        char c = buffer[i];
        if (flags & os.uppercase && (('a' <= c && c <= 'f') || c == 'x'))
            out_buffer[i] = os.widen(c - 32);
        else
            out_buffer[i] = os.widen(c);
    }

    if (!(flags & os.internal)) {
        if (flags & os.right || (flags & os.adjustfield) == 0)
            for (ptrdiff_t i = 0; i < lw; i++) os.put(fillch);
        os.write(out_buffer, nl);
        if (flags & os.left)
            for (ptrdiff_t i = 0; i < lw; i++) os.put(fillch);
    } else {
        if (pos) os.write(out_buffer, pos);
        for (ptrdiff_t i = 0; i < lw; i++) os.put(fillch);
        os.write(out_buffer + pos, nl - pos);
    }

    return os;
}

template <class CharT, class Traits, size_t B, class D, bool S>
basic_istream<CharT, Traits>& operator>>(
    basic_istream<CharT, Traits>& is, fwnbi::basic_integer<B, D, S>& value
) {
    const auto flags = is.flags();
    auto peek_ch = [&is] () -> char { return is.narrow(Traits::to_char_type(is.peek()), EOF); };
    auto get_ch  = [&is] () -> char { return is.narrow(Traits::to_char_type(is. get()), EOF); };
    value.clear();

    if (!(flags & is.skipws)) {
        if (fwnbi::detail::cexpr_isspace(peek_ch()))
            { is.setstate(is.failbit); return is; }
        else if (is.peek() == Traits::eof())
            { is.setstate(is.eofbit); return is; }
    } else while (fwnbi::detail::cexpr_isspace(peek_ch()))
        is.ignore(1);

    bool sign = false;
    switch (peek_ch()) {
        case '-': sign = true;
            /* fallthrough */
        case '+': is.ignore(1);
    }

    int base = 10;
    /**/ if (flags & is.oct) base = 8;
    else if (flags & is.hex) {
        base = 16;
        if (peek_ch() == '0') {
            is.ignore(1);
            if (peek_ch() == 'x' || peek_ch() == 'X')
                is.ignore(1);
        }
    }

    if (sign && !(flags & is.dec))
        { is.setstate(is.failbit); return is; }

    while (true) {
        if (is.peek() == Traits::eof())
            { is.setstate(is.eofbit); break; }

        if (fwnbi::detail::char2digit<D>(peek_ch()) == D(-1))
            { is.setstate(is.failbit); break; }
        const D next = fwnbi::detail::char2digit<D>(get_ch());
        if (next >= D(base)) break;

        if (base == 10) {
            bool carry = false;
            fwnbi::basic_integer<B, D, S> num_c = value << 3;
            carry |= value.bit(B-S-1) || value.bit(B-S-2) || value.bit(B-S-3);
            carry |= num_c.add_with_carry(value << 1);
            carry |= num_c.add_with_carry(next);
            if (carry) {
                is.setstate(is.failbit);
                value = fwnbi::basic_integer<B, D, S>::max();
                break;
            }
            value = num_c;
        } else {
            const bool is_hex = base == 16;
            if (value.hex(B/4 - 1) >> is_hex) {
                is.setstate(is.failbit);
                value = fwnbi::basic_integer<B, D, S>::max();
                break;
            }
            value <<= 3 + is_hex;
            value[0] |= next;
        }
    }

    if (sign) value = -value;

    return is;
}

#if __cplusplus >= 201703L

template <size_t B, class D, bool S>
constexpr to_chars_result to_chars(char* first, char* last,
    const fwnbi::basic_integer<B, D, S>& value, int base = 10
) noexcept {
    if (base < 2 || base > 36)
        return {last, errc::invalid_argument};

    bool of = false; char* end = nullptr;
    switch (base) {
        case  2: end = fwnbi::detail::to_chars_pow2(first, last, value, &of, 1); break;
        case  4: end = fwnbi::detail::to_chars_pow2(first, last, value, &of, 2); break;
        case  8: end = fwnbi::detail::to_chars_pow2(first, last, value, &of, 3); break;
        case 16: end = fwnbi::detail::to_chars_pow2(first, last, value, &of, 4); break;
        case 32: end = fwnbi::detail::to_chars_pow2(first, last, value, &of, 5); break;
        default: end = fwnbi::detail::to_chars_i(first, last, value, &of, base); break;
    }

    if (of) return {last, errc::value_too_large};
    return {end, errc{}};
}

template <size_t B, class D, bool S>
constexpr from_chars_result from_chars(
    const char* first, const char* last,
    fwnbi::basic_integer<B, D, S>& value, int base = 10
) noexcept {
    if (base < 2 || base > 36)
        return {first, errc::invalid_argument};

    from_chars_result out{first, errc{}};
    auto res = fwnbi::detail::from_char_res::ok;
    const fwnbi::basic_integer<B, D, S> parsed =
        fwnbi::detail::from_chars_i<B, D, S>(first, last, res, &out.ptr, base);

    switch (res) {
        case fwnbi::detail::from_char_res::ok: value = parsed; break;
        case fwnbi::detail::from_char_res::overflow:
            out.ec = errc::result_out_of_range; break;
        case fwnbi::detail::from_char_res::invalid:
            out.ec = errc::invalid_argument; break;
    }

    return out;
}

#endif // __cplusplus >= 201703L

#if __cplusplus >= 202002L

template <size_t B, class D, bool S>
struct formatter<fwnbi::basic_integer<B, D, S>, char> {
private:
    enum class fmt_base  { bin, Bin, oct, dec, hex, Hex };
    enum class fmt_align { none, left, center, right };
    enum class fmt_sign  { none, plus, space };

private:
    fmt_align align = fmt_align::none;
    fmt_sign  sign  = fmt_sign ::none;
    fmt_base  base  = fmt_base ::dec;
    bool use_zero_fill = false;
    bool width_is_arg  = false;
    bool use_prefix    = false;
    size_t width_id = 0;
    int    width    = 0;
    char fill_char = ' ';

public:
    constexpr typename basic_format_parse_context<char>::iterator
    parse(basic_format_parse_context<char>& ctx) {
        auto it = ctx.begin();
        if (it == ctx.end())
            return it;

        if (*it != '{' && *it != '}' && it + 1 != ctx.end() &&
            (it[1] == '<' || it[1] == '^' || it[1] == '>'))
            fill_char = *it++;
        if (*it == '<' || *it == '^' || *it == '>')
            switch (*it++) {
                case '<': align = fmt_align::left;   break;
                case '^': align = fmt_align::center; break;
                case '>': align = fmt_align::right;  break;
            }

        if (it != ctx.end() && *it == '#')
            { use_prefix = true; ++it; }

        if (it != ctx.end() && *it == '0')
            { use_zero_fill = true; ++it; }

        if (it != ctx.end()) {
            /*  */ if (*it != '0' && fwnbi::detail::cexpr_isdigit(*it)) {
                while (it != ctx.end() && fwnbi::detail::cexpr_isdigit(*it))
                    width = width * 10 + ((*it++) - '0');
            } else if (*it == '{') {
                width_is_arg = true; ++it;
                /*  */ if (it != ctx.end() && *it == '}') {
                    width_id = ctx.next_arg_id(); ++it;
                } else {
                    while (it != ctx.end() && fwnbi::detail::cexpr_isdigit(*it))
                        width_id = width_id * 10 + ((*it++) - '0');
                    if (it == ctx.end() || *it != '}')
                        throw format_error("Invalid width index");
                    ctx.check_arg_id(width_id); ++it;
                }
            }
        }

        if (it != ctx.end())
            switch (*it++) {
                case 'b': base = fmt_base::bin; break;
                case 'B': base = fmt_base::Bin; break;
                case 'o': base = fmt_base::oct; break;
                case 'd': base = fmt_base::dec; break;
                case 'x': base = fmt_base::hex; break;
                case 'X': base = fmt_base::Hex; break;
                default : --it; break;
            }

        if (it != ctx.end() && *it != '}')
            throw format_error("Invalid specification for fwnbi::basic_integer");
        return it;
    }

    template <class Out>
    typename basic_format_context<Out, char>::iterator format(
        const fwnbi::basic_integer<B, D, S>& value,
        basic_format_context<Out, char>& ctx
    ) const {
        char buffer[B + 4] {}, *end;
        size_t pos = 0;

        if (base == fmt_base::dec && sign != fmt_sign::none && value.sign() >= 0) {
            if (sign == fmt_sign::plus ) buffer[pos++] = '+';
            if (sign == fmt_sign::space) buffer[pos++] = ' ';
        }

        if (base != fmt_base::dec && use_prefix) {
            buffer[pos++] = '0';
            if (base == fmt_base::bin) buffer[pos++] = 'b';
            if (base == fmt_base::Bin) buffer[pos++] = 'B';
            if (base == fmt_base::hex) buffer[pos++] = 'x';
            if (base == fmt_base::Hex) buffer[pos++] = 'X';
        }

        switch (base) {
            case fmt_base::dec:
                end = fwnbi::detail::to_chars_i(buffer + pos,
                    buffer + sizeof buffer, value, nullptr, 10);
                break;
            case fmt_base::bin:
            case fmt_base::Bin:
                end = fwnbi::detail::to_chars_pow2(buffer + pos,
                    buffer + sizeof buffer, value, nullptr, 1);
                break;
            case fmt_base::oct:
                end = fwnbi::detail::to_chars_pow2(buffer + pos,
                    buffer + sizeof buffer, value, nullptr, 3);
                break;
            case fmt_base::hex:
            case fmt_base::Hex:
                end = fwnbi::detail::to_chars_pow2(buffer + pos,
                    buffer + sizeof buffer, value, nullptr, 4,
                    base == fmt_base::Hex); break;
        }

        ptrdiff_t field_width;
        if (width_is_arg) {
            auto visitor = [](auto v) -> ptrdiff_t {
                if constexpr (!is_integral_v<decltype(v)>)
                    throw format_error("Width is not integer");
                else if (v < 0 || v > numeric_limits<ptrdiff_t>::max())
                    throw format_error("Invalid width value");
                else
                    return static_cast<ptrdiff_t>(v);
            };
#if 0 // TODO: replace to check is C++26
            field_width = ctx.arg(width_id).visit(visitor);
#else
            field_width = visit_format_arg(visitor, ctx.arg(width_id));
#endif
        } else
            field_width = width;

        auto out = ctx.out();
        ptrdiff_t n = field_width - (end - buffer);

        switch (align) {
            case fmt_align::none: {
                char* buf_begin = buffer + (
                    base != fmt_base::dec &&
                    base != fmt_base::oct &&
                    use_prefix ? 2 : 0);
                out = copy(buffer, buf_begin, out);
                if (use_zero_fill && n > 0)
                    for (size_t i = n; i --> 0;) *out++ = '0';
                out = copy(buf_begin, end, out);
            } break;
            case fmt_align::left: {
                out = copy(buffer, end, out);
                if (n > 0) for (size_t i = n; i --> 0;) *out++ = fill_char;
            } break;
            case fmt_align::right: {
                if (n > 0) for (size_t i = n; i --> 0;) *out++ = fill_char;
                out = copy(buffer, end, out);
            } break;
            case fmt_align::center: {
                if (  n/2 > 0) for (size_t i =   n/2; i --> 0;) *out++ = fill_char;
                out = copy(buffer, end, out);
                if (n-n/2 > 0) for (size_t i = n-n/2; i --> 0;) *out++ = fill_char;
            } break;
        }

        return out;
    }
};

#endif // __cplusplus >= 202002L

} // namespace std

#endif // FIXED_WIDTH_N_BITS_INTEGERS_HPP