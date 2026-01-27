import Mathlib

set_option linter.style.emptyLine false

notation "φ" => Nat.totient

theorem eulers {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) : a ^ φ n = 1 := by

  let A := Subgroup.zpowers a
  have : Nat.card A ∣ Nat.card (ZMod n)ˣ := by
    exact Subgroup.card_subgroup_dvd_card A

  rw [Nat.card_zpowers, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this
  /- this : orderOf a ∣ φ n -/

  obtain ⟨m, h⟩ := this
  rw [h, pow_mul, pow_orderOf_eq_one, one_pow]

theorem eulers_mod_arith {n a : ℕ} [NeZero n] (h : a.Coprime n)
    : a ^ φ n ≡ 1 [MOD n] := by

  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← ZMod.coe_unitOfCoprime a h]
  rw [← Units.val_pow_eq_pow_val]
  rw [eulers (ZMod.unitOfCoprime a h)]
  rfl

theorem fermats_little_theorem {p a : ℕ} (hp : p.Prime) (hpn : a.Coprime p)
    : a ^ (p - 1) ≡ 1 [MOD p] := by

  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← ZMod.coe_unitOfCoprime a hpn]
  rw [← Units.val_pow_eq_pow_val]

  have : NeZero p := ⟨Nat.Prime.ne_zero hp⟩

  rw [← Nat.totient_prime hp]
  rw [eulers (ZMod.unitOfCoprime a hpn)]
  rfl

