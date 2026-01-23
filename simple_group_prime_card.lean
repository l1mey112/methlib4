import Mathlib

set_option linter.style.emptyLine false

/- g : G for g ∈ G (type theory)
  do not write ∃g ∈ G, this doesn't make sense!

  but g ∈ H, for H : Subgroup G (set theory) -/

theorem neq_one_zpowers_eq_top {G : Type*} [Group G]
    {g : G} (h : g ≠ 1)
    (h₀ : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)
    : Subgroup.zpowers g = ⊤ := by

  /- There are two cases, either any subgroup H = 1 or H = G. -/
  rcases h₀ (Subgroup.zpowers g) with eq_triv | eq_G
  · /- If ⟨g⟩ = 1, then g = 1. -/
    rw [Subgroup.zpowers_eq_bot] at eq_triv

    /- But g ≠ 1, by assumption. -/
    have := h
    contradiction

  · /- If ⟨g⟩ = G, we wanted to show this anyway. -/
    assumption

theorem not_isOfFinOrder_pow_neq_one {G : Type*} [Group G] {g : G} {k : Nat} (hk : k > 0)
    (h : ¬IsOfFinOrder g)
    : g ^ k ≠ 1 := by

  by_contra
  have : IsOfFinOrder g := by
    rw [isOfFinOrder_iff_pow_eq_one]
    use k

  contradiction

theorem exists_mem_bot_eq_zpowers {G : Type*} [Group G] [Nontrivial G]
    (h₀ : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)
    : ∃g : G, Subgroup.zpowers g = ⊤ := by

  /- There exist an element g ∈ G such that g ≠ 1. -/
  have ⟨g, h⟩ := Subgroup.exists_ne_one_of_nontrivial (⊤ : Subgroup G)

  /- It suffices to provide an element g ∈ G and a proof that G = ⟨g⟩. -/
  use g
  exact neq_one_zpowers_eq_top h.2 h₀

/-

1. assume G is infinite. but then ⟨g²⟩, ⟨g³⟩, ... are subgroups of G.
   contradiction!

2. G is finite. Then, we can take n = |G| = |g|

3. if n is prime, we are done.
   if n is not prime, then n = mn for natural numbers m, n.

4. but, since m ∣ |g|, there exist a subgroup ⟨g^m⟩ ≠ ⟨g⟩
   contradiction!

conclusion:
- G is finite
- |g| = |G| = n is prime

-/

theorem prime_card {G : Type*} [Group G] [Nontrivial G]
    (hc : IsCyclic G) (h₀ : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)
    : (Nat.card G).Prime := by

  have ⟨g, h_generator_eq_top⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hc

  have g_neq_one : g ≠ 1 := by
    intro g_eq_one
    rw [g_eq_one, Subgroup.zpowers_one_eq_bot] at h_generator_eq_top

    /- Subgroup relation is a partial order.
       If lattice of Subgroup G is nontrivial, then ⊤ ≠ ⊥. (G ≠ 1) -/

    have : (⊥ : Subgroup G) ≠ ⊤ := bot_ne_top
    contradiction

  by_cases h : Infinite G
  · /- If G = ⟨g⟩ is infinite, then ⟨g²⟩, ⟨g³⟩, ... subgroups of G,
       a contradiction. -/

    have ginf : ¬IsOfFinOrder g := by
      intro finorder
      /- If g is of finite order, then ⊤ = ⟨g⟩ is of finite order. -/
      have h_sub_fin : Finite (Subgroup.zpowers g) := IsOfFinOrder.finite_zpowers finorder
      rw [h_generator_eq_top] at h_sub_fin

      /- (⊤ : Subgroup G) and G are equinumerous, but ⊤ is Finite and G is Infinite. -/
      have : Finite G := Finite.of_equiv ↥(⊤ : Subgroup G) (Subgroup.topEquiv.toEquiv)
      exact this.not_infinite h

    have two_neq : Subgroup.zpowers g ≠ Subgroup.zpowers (g * g) := by
      by_contra h
      rw [Subgroup.zpowers_eq_zpowers_iff ginf] at h
      rcases h with h1 | h2
      · /- g = g² ↔ g = 1 -/
        /- But g is of infinite order, a contradiction. -/
        rw [left_eq_mul] at h1
        rw [h1] at ginf
        have : IsOfFinOrder (1 : G) := IsOfFinOrder.one
        contradiction

      · /- g⁻¹ = g² ↔ g³ = 1 -/
        /- But g is of infinite order, a contradiction. -/
        rw [inv_eq_iff_mul_eq_one, ← pow_three] at h2
        have h_is_fin : IsOfFinOrder g := by
          rw [isOfFinOrder_iff_pow_eq_one]
          use 3
          simpa

        contradiction

    have p1 : Subgroup.zpowers g = ⊤ := by
      exact neq_one_zpowers_eq_top g_neq_one h₀

    have p2 : Subgroup.zpowers (g * g) = ⊤ := by
      have : g * g ≠ 1 := by
        rw [← pow_two]
        exact not_isOfFinOrder_pow_neq_one (by decide) ginf
      exact neq_one_zpowers_eq_top this h₀

    -- p1 : Subgroup.zpowers g = ⊤
    -- p2 : Subgroup.zpowers (g * g) = ⊤

    rw [← p2] at p1
    contradiction
  · have h : Finite G := by rwa [← not_infinite_iff_finite]

    /- ⊢ Nat.Prime (orderOf g) -/
    rw [← orderOf_eq_card_of_zpowers_eq_top h_generator_eq_top]

    by_contra orderOf_prime
    have two_le_orderOf : 2 ≤ orderOf g := by
      have := orderOf_pos g
      have : orderOf g ≠ 1 := by simp_all
      omega

    /- Well, if |g| is not prime, then |g| = mn for natural numbers m, n. -/
    have ⟨m, n, ⟨_, _, h⟩⟩ := (Nat.not_prime_iff_exists_mul_eq two_le_orderOf).mp orderOf_prime

    /- That is, m ∣ |g|. -/
    have m_dvd_orderOf_g : m ∣ (orderOf g) := by
      use n; exact h.symm

    /- If there exist m ∣ |g|, then there exist a subgroup of order m, a contradiction. -/

    let g' := g^(orderOf g / m)
    have orderOf_g'_eq_m : orderOf g' = m := orderOf_pow_orderOf_div (by omega) m_dvd_orderOf_g

    have g'_neq_one : g' ≠ 1 := by
      by_contra g_eq_one
      have orderOf_g'_eq_one : orderOf g' = 1 := by
        rw [g_eq_one]
        exact orderOf_one

      have : m = 1 := by
        rw [← orderOf_g'_eq_m, orderOf_g'_eq_one]

      /- TODO: how the fuck did grind get this... -/
      have : m ≠ 1 := by grind
      contradiction

    -- 1. ⟨g⟩ = ⟨g'⟩ by h₀
    -- 2. |⟨g⟩| = |⟨g'⟩|
    -- 3. orderOf g = orderOf g'
    --    contradiction!
    have : orderOf g = orderOf g' := by
      rw [orderOf_eq_card_of_zpowers_eq_top h_generator_eq_top]
      rw [orderOf_eq_card_of_zpowers_eq_top (neq_one_zpowers_eq_top g'_neq_one h₀)]

    /- h : orderOf g = orderOf g' -/
    have : orderOf g ≠ orderOf g' := by
      omega

    contradiction

/-
Theorem. A nontrivial group with only subgroups 1 or G is isomorphic to Zₚ for some prime p.
-/
theorem nontrivial_cyclic_and_prime_card {G : Type*} [Group G] [Nontrivial G]
    (h₀ : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤)
    : IsCyclic G ∧ (Nat.card G).Prime := by

  have exist_g := exists_mem_bot_eq_zpowers h₀

  /- We know it's cyclic, as proven above. -/
  have hc : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact exist_g

  constructor
  · exact hc               /- IsCyclic G -/
  · exact prime_card hc h₀ /- |G|.Prime -/

/--
info: 'nontrivial_cyclic_and_prime_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nontrivial_cyclic_and_prime_card

/-
Theorem. A abelian simple group is isomorphic to Zₚ for some prime p.
-/
theorem IsSimpleGroup.cyclic_and_prime_card {G : Type*} [CommGroup G] [h : IsSimpleGroup G]
    : IsCyclic G ∧ (Nat.card G).Prime := by

  have h₀ : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤ := by
    intro H
    exact h.eq_bot_or_eq_top_of_normal H (Subgroup.normal_of_comm H)

  exact nontrivial_cyclic_and_prime_card h₀

/-
This is a much stronger classification of Abelian simple groups. In mathlib they only do this
correspondance for finite Abelian simple groups. We do not assume [Finite G].
-/
#check IsSimpleGroup.prime_card

