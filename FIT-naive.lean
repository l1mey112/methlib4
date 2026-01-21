import Mathlib

set_option linter.style.emptyLine false

noncomputable section

/- our two groups G and H -/
variable {G H : Type*} [Group G] [Group H]

/- we know φ is a homomorphism -/
variable {φ : G →* H}

lemma eq_iff_mem_ker (g₁ g₂ : G)
    : φ g₁ = φ g₂ ↔ g₁⁻¹ * g₂ ∈ φ.ker := by

  /- φ g₁ = φ g₂ -/
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul]
  rw [MonoidHom.mem_ker]

/-- Canonical Homomorphism π : G ⧸ ker φ → φ(G). -/
def π : G ⧸ φ.ker → φ.range := by
  intro x

  refine ⟨?_, ?_⟩
  · refine Quotient.lift φ ?_ x
    intro g₁ g₂ h
    /- g₁ ≈ g₂ → φ g₁ = φ g₂ -/

    /- we have g₁K = g₂K if and only if g₁⁻¹ g₂ ∈ K -/
    have hrel : g₁⁻¹ * g₂ ∈ φ.ker := by
      rwa [← QuotientGroup.leftRel_apply]

    rwa [eq_iff_mem_ker]

  · induction x using Quotient.inductionOn with
    | h a =>
      rw [Quotient.lift_mk]
      rw [MonoidHom.mem_range]
      use a

/- monoid homomorphisms are exactly group homomorphisms, but
   for monoids preserving mul doesn't imply that you preserve
   the identity.

   use `MonoidHom.mk'` to use the group instance -/

def π_hom : G ⧸ φ.ker →* φ.range :=
  MonoidHom.mk' π (by
    intro x y

    /- π (g₁ * g₂) = π g₁ * π g₂ -/
    simp only [π, MulMemClass.mk_mul_mk, Subtype.mk.injEq]

    induction x using Quotient.inductionOn with
    | h g₁ =>
    induction y using Quotient.inductionOn with
    | h g₂ =>

    rw [← QuotientGroup.mk_mul]
    repeat rw [Quotient.lift_mk]

    /- φ (g₁ * g₂) = φ g₁ * φ g₂     (φ is a homomorphism) -/
    exact MonoidHom.map_mul φ g₁ g₂
  )

theorem π_bijective : Function.Bijective (π : G ⧸ φ.ker → φ.range) := by
  constructor
  · intro x y h

    /- π (g₁ * g₂) = π g₁ * π g₂ -/
    induction x using Quotient.inductionOn with
    | h g₁ =>
    induction y using Quotient.inductionOn with
    | h g₂ =>

    simp only [π, Quotient.lift_mk, Subtype.mk.injEq] at h

    rw [QuotientGroup.eq]
    rwa [eq_iff_mem_ker] at h

  · intro y
    /- we know that y ∈ φ.range, hence ∃g, φ g = y -/
    obtain ⟨g, hg⟩ := y.property

    unfold π
    rw [QuotientGroup.exists_mk]; use g

    ext
    simpa

def FIT : G ⧸ φ.ker ≃* (φ.range) := by
  exact MulEquiv.ofBijective π_hom π_bijective

/--
info: 'FIT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FIT
