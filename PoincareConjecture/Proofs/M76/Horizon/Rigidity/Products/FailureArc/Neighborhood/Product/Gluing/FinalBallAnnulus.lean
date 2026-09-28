import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Assembly

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem exists_final_ball_annular_collar
    {X : Type} [TopologicalSpace X] [T2Space X]
    {B : Set X}
    (H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
      ∃ a : (Rim : Set P2) × I → X,
        ∃ q : (Rim : Set P2) → (Disk : Set P2),
          Function.Injective a ∧
          (∀ z t, (HB (q z, t) : X) = a (z, t)) ∧
          (∀ y t, (HB (y, t) : X) ∈ range a ↔ ∃ z, q z = y) := by
  obtain ⟨HB, _⟩ := ProductConstruction.exists_subtype_product_final_ball H
  let q : (Rim : Set P2) → (Disk : Set P2) := fun z =>
    ⟨z.1, sphere_subset_closedBall z.2⟩
  let a : (Rim : Set P2) × I → X := fun p => HB (q p.1, p.2)
  refine ⟨HB, a, q, ?_, ?_, ?_⟩
  · intro p p' hpp'
    have hHB : HB (q p.1, p.2) = HB (q p'.1, p'.2) :=
      Subtype.ext hpp'
    have hp : (q p.1, p.2) = (q p'.1, p'.2) := HB.injective hHB
    have hpval := congrArg (fun z : (Disk : Set P2) × I =>
      ((z.1 : P2), (z.2 : ℝ))) hp
    have hfirst : p.1 = p'.1 :=
      Subtype.ext (congrArg Prod.fst hpval)
    exact Prod.ext hfirst (Subtype.ext (congrArg Prod.snd hpval))
  · intro z t
    rfl
  · intro y t
    constructor
    · rintro ⟨p, hp⟩
      change (HB (q p.1, p.2) : X) = (HB (y, t) : X) at hp
      have hHB : HB (q p.1, p.2) = HB (y, t) := Subtype.ext hp
      have hbase : (q p.1, p.2) = (y, t) := HB.injective hHB
      exact ⟨p.1, congrArg Prod.fst hbase⟩
    · rintro ⟨z, hzy⟩
      subst y
      exact ⟨(z, t), rfl⟩

theorem exists_final_ball_marked_annular_collar
    {X : Type} [TopologicalSpace X] [T2Space X]
    {B : Set X} (H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B)
    {k : P2 × ℝ → X} {a₀ : P2 × ℝ → X}
    (hkv : ∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X))
    (hann : EqOn k a₀ (Rim ×ˢ I)) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
      ∃ a : (Rim : Set P2) × I → X,
        ∃ q : (Rim : Set P2) → (Disk : Set P2),
          Function.Injective a ∧
          (∀ z t, (HB (q z, t) : X) = a (z, t)) ∧
          (∀ y t, (HB (y, t) : X) ∈ range a ↔ ∃ z, q z = y) ∧
          (∀ z t, a (z, t) = a₀ (z.1, t.1)) ∧
          (∀ z t, (HB (z, t) : X) = k (z.1, t.1)) := by
  obtain ⟨HB, hHB⟩ := ProductConstruction.exists_subtype_product_final_ball H
  let q : (Rim : Set P2) → (Disk : Set P2) := fun z =>
    ⟨z.1, sphere_subset_closedBall z.2⟩
  let a : (Rim : Set P2) × I → X := fun p => HB (q p.1, p.2)
  have hbase (z : (Rim : Set P2)) (t : I) :
      (HB (q z, t) : X) = k (z.1, t.1) := by
    rw [hHB]
    rw [← hkv]
    rfl
  have ha : Function.Injective a := by
    intro p p' hpp'
    have hHB' : HB (q p.1, p.2) = HB (q p'.1, p'.2) :=
      Subtype.ext hpp'
    have hp : (q p.1, p.2) = (q p'.1, p'.2) := HB.injective hHB'
    have hpval := congrArg (fun z : (Disk : Set P2) × I =>
      ((z.1 : P2), (z.2 : ℝ))) hp
    have hfirst : p.1 = p'.1 := Subtype.ext (congrArg Prod.fst hpval)
    exact Prod.ext hfirst (Subtype.ext (congrArg Prod.snd hpval))
  have hparam : ∀ z t, (HB (q z, t) : X) = a (z, t) := by
    intro z t
    rfl
  have hside : ∀ y t, (HB (y, t) : X) ∈ range a ↔ ∃ z, q z = y := by
    intro y t
    constructor
    · rintro ⟨p, hp⟩
      change (HB (q p.1, p.2) : X) = (HB (y, t) : X) at hp
      have hHB' : HB (q p.1, p.2) = HB (y, t) := Subtype.ext hp
      have hbase' : (q p.1, p.2) = (y, t) := HB.injective hHB'
      exact ⟨p.1, congrArg Prod.fst hbase'⟩
    · rintro ⟨z, hzy⟩
      subst y
      exact ⟨(z, t), rfl⟩
  refine ⟨HB, a, q, ha, hparam, hside, ?_, ?_⟩
  · intro z t
    change (HB (q z, t) : X) = a₀ (z.1, t.1)
    rw [hbase]
    exact hann ⟨z.2, t.2⟩
  · intro z t
    rw [hHB, ← hkv]
    rfl

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
