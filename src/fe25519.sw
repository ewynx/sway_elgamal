library;

use signed_integers::i64::I64;
use std::flags::{disable_panic_on_overflow, enable_panic_on_overflow};

// fe25519 slides https://cryptojedi.org/peter/data/pairing-20131122.pdf
// toy impl https://github.com/ewynx/golang_fe25519/blob/master/fp25519.go
// Sway docs https://fuellabs.github.io/sway/v0.48.1/book

pub struct BigInt256 {
  // 5 limbs of max 64 bits, in reduces form 51 bits
  l: [I64; 5]
}

fn wrapping_sub(lhs: u64, rhs: u64) -> u64 {
    if lhs >= rhs {
        lhs - rhs
    } else {
        u64::max() - (rhs - lhs - 1)
    }
}

fn wrapping_add(lhs: u64, rhs: u64) -> u64 {
    disable_panic_on_overflow(); 
    let overflow = asm(overflow, r1: lhs, r2: rhs, r3) {
        add r3 r1 r2; // r3 = r1 + r2
        move overflow of; // move the underflow (which goes into $of automatically) to a variable (named overflow)
        overflow
    };
    enable_panic_on_overflow();

    if overflow != 0 {
        // Overflow occurred
        return u64::max() - (lhs - (rhs-1));
    } else {
        // No overflow
        return lhs + rhs;
    }
}

fn rsh(value: I64, shift: u64) -> I64 {
    let signed_value = wrapping_sub(value.underlying, I64::indent());
    let shifted_signed_value = signed_value >> shift;
    I64::from(shifted_signed_value)
}

fn lsh(value: I64, shift: u64) -> I64 {
    let signed_value = wrapping_sub(value.underlying, I64::indent());
    let shifted_signed_value = signed_value << shift;
    I64::from(shifted_signed_value)
}


impl BigInt256 {
  fn zero() -> Self {
    BigInt256 { l: [I64::new(); 5]}
  }

  fn new(limbs: [I64; 5]) -> Self {
    BigInt256 { l: limbs}
  }

  fn from_u64arr(limbs: [u64; 5]) -> Self {
    BigInt256 { l: [
      I64::from(limbs[0]),
      I64::from(limbs[1]),
      I64::from(limbs[2]),
      I64::from(limbs[3]),
      I64::from(limbs[4])
    ]}
  }
}

// Can't use a function defined in the same `impl`
// known issue https://fuellabs.github.io/sway/v0.48.1/book/reference/known_issues_and_workarounds.html
impl BigInt256 {
  fn add(self, b: Self) -> Self {
    let mut res = Self::zero();
    let mut i = 0;
    while i < 5 {
      res.l[i] = self.l[i] + b.l[i];
      i += 1;
    }
    return res;
  }

  fn sub(self, b: Self) -> Self {
    let mut res = Self::zero();
    let mut i = 0;
    while i < 5 {
      res.l[i] = self.l[i] - b.l[i];
      i += 1;
    }
    return res;
  }

  fn reduce(ref mut self){
    let mut carry = I64::new();
    let mut i = 0;
    while i < 4 {
      carry = rsh(self.l[i], 51);
      self.l[i+1] = self.l[i+1] + carry;
      carry = lsh(carry, 51);
      self.l[i] = self.l[i] - carry;
      i += 1;
    }
    carry = rsh(self.l[4], 51);
    self.l[0] = self.l[0] + I64::from(19)*carry;
    carry = lsh(carry, 51);
    self.l[4] = self.l[4] - carry;
  }
}

fn equals(check: BigInt256, expected: [u64;5]) {
  assert(check.l[0] == I64::from(expected[0]));
  assert(check.l[1] == I64::from(expected[1]));
  assert(check.l[2] == I64::from(expected[2]));
  assert(check.l[3] == I64::from(expected[3]));
  assert(check.l[4] == I64::from(expected[4]));
}

fn equals_i64arr(check: BigInt256, expected: [I64;5]) {
  assert(check.l[0] == expected[0]);
  assert(check.l[1] == expected[1]);
  assert(check.l[2] == expected[2]);
  assert(check.l[3] == expected[3]);
  assert(check.l[4] == expected[4]);
}


#[test]
fn test_add() {
  /*
  a_limbs: [1304166785643154, 86409186782748, 935970054375578, 2119670992843881, 828063237092988]
  b_limbs: [2132282820181009, 459020425946617, 289774753638479, 1005253865020125, 1771263444419705]
  expected: [3436449605824163, 545429612729365, 1225744808014057, 3124924857864006, 2599326681512693]
  */
    let a = BigInt256::from_u64arr([1304166785643154, 86409186782748, 935970054375578, 2119670992843881, 828063237092988]);
    let b = BigInt256::from_u64arr([2132282820181009, 459020425946617, 289774753638479, 1005253865020125, 1771263444419705]);
    let res = a.add(b);

    let expected = [3436449605824163, 545429612729365, 1225744808014057, 3124924857864006, 2599326681512693];

    equals(res, expected);
}

#[test]
fn test_add_and_sub() {
  /*
  a_limbs: [452128870718638, 1599889009582867, 126713692126506, 1851403528960825, 270922399293928]
  b_limbs: [2208520496760492, 2014504343533248, 2223780781734281, 1104930181197456, 1832479852831237]
  expected_add: [2660649367479130, 3614393353116115, 2350494473860787, 2956333710158281, 2103402252125165]
  expected_sub: [-1756391626041854, -414615333950381, -2097067089607775, 746473347763369, -1561557453537309]
  */

    let a = BigInt256::from_u64arr([452128870718638, 1599889009582867, 126713692126506, 1851403528960825, 270922399293928]);
    let b = BigInt256::from_u64arr([2208520496760492, 2014504343533248, 2223780781734281, 1104930181197456, 1832479852831237]);

    let res_add = a.add(b);
    let res_sub = a.sub(b);

    let expected_add = [2660649367479130, 3614393353116115, 2350494473860787, 2956333710158281, 2103402252125165];
    
    let expected_sub = [
      I64::neg_from(1756391626041854),
      I64::neg_from(414615333950381),
      I64::neg_from(2097067089607775),
      I64::from(746473347763369),
      I64::neg_from(1561557453537309)
    ];
    
    equals(res_add, expected_add);
    equals_i64arr(res_sub, expected_sub);
}

#[test]
fn test_wrapping_sub() {
    let result1 = wrapping_sub(10, 5);
    assert(result1 == 5);

    let result2 = wrapping_sub(5, 10);
    assert(result2 == u64::max() - 4);
}

#[test]
fn test_wrapping_add() {
    let result1 = wrapping_add(10, 5);
    assert(result1 == 15);

    let result2 = wrapping_add(u64::max(), 2);
    assert(result2 == 1);
}

#[test]
fn test_rsh() {
    let value = I64::from(8);
    let shift = 2;
    let expected_result = I64::from(2);
    let rsh_result = rsh(value, shift);

    assert(rsh_result == expected_result);
}

#[test]
fn test1_reduce() {
    let mut a = BigInt256::from_u64arr([0, 0, 0, 0, 0]);
    let expected = [0, 0, 0, 0, 0];
    a.reduce();
    
    equals(a, expected);
}

#[test]
fn test2_reduce() {
    let mut a = BigInt256::from_u64arr([4503599627370495, 1, 1, 1, 1]);
    let expected = [2251799813685247, 2, 1, 1, 1];
    a.reduce();
    
    equals(a, expected);
}

#[test]
fn test3_reduce() {
    let mut a = BigInt256::from_u64arr([4503599627370495, 4503599627370495, 4503599627370495, 4503599627370495, 4503599627370495]);
    let expected = [37, 1, 1, 1, 1];
    // Needs 2 rounds of reducing
    a.reduce();
    a.reduce();
    
    equals(a, expected);
}

#[test]
fn test4_reduce() {
    let mut a = BigInt256::from_u64arr([9223372036854775807, 0, 0, 0, 0]);
    let expected = [2251799813685247, 4095, 0, 0, 0];
    a.reduce();
    
    equals(a, expected);
}