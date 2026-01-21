import Mathlib

set_option linter.style.emptyLine false

noncomputable section

/- Our two groups G and H. -/
variable {G H : Type*} [Group G] [Group H]

/- We know φ is a homomorphism. -/
variable {φ : G →* H}

lemma hom_eq_iff_mem_ker (g₁ g₂ : G)
    : φ g₁ = φ g₂ ↔ g₁⁻¹ * g₂ ∈ φ.ker := by

  /- φ g₁ = φ g₂ -/
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul]
  rw [MonoidHom.mem_ker]

/-- Kernel of φ is contained within φ.rangeRestrict : G → φ.range. -/
theorem φ_ker_le_f_ker : φ.ker ≤ φ.rangeRestrict.ker := by
  /- φ.ker ≤ f.ker -/
  intro g mem
  rw [MonoidHom.mem_ker]
  ext -- `ext` is the best way to deal with ∈ φ.range
  simpa

/-- We can define the homomorphism ψ(gK) = φ(g) from the universal property. -/
def ψ : G ⧸ φ.ker →* φ.range := QuotientGroup.lift φ.ker φ.rangeRestrict (φ_ker_le_f_ker)

/-- Homomorphism ψ is bijective. -/
theorem ψ_bijective : Function.Bijective (ψ (φ := φ)) := by
  constructor
  · intro x y
    /- see QuotientGroup.rangeKerLift_injective -/
    refine Quotient.inductionOn₂' x y
      fun a b (h : φ.rangeRestrict a = φ.rangeRestrict b) => Quotient.sound' ?_

    /- a ≈ b ↔ a⁻¹ * b ∈ φ.ker -/
    rw [QuotientGroup.leftRel_apply]

    /-
      h : φ a = φ b
      ⊢ a⁻¹ * b ∈ φ.ker
    -/
    rw [← MonoidHom.ker_rangeRestrict]
    rwa [hom_eq_iff_mem_ker] at h

  · /- We know that φ.rangeRestrict : G → φ.range is surjective by definition.  -/
    exact QuotientGroup.lift_surjective_of_surjective φ.ker φ.rangeRestrict
      φ.rangeRestrict_surjective φ_ker_le_f_ker

def FIT : G ⧸ φ.ker ≃* (φ.range) := by
  exact MulEquiv.ofBijective ψ ψ_bijective
