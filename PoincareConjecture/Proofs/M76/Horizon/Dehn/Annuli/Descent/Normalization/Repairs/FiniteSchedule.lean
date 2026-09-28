import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.ExceptionRepair









set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}

structure FiniteAnnulusRepairs (D : OriginalRelativeNormalization step K j R Rim) where
  size : ℕ
  window : Fin size → Set s.Carrier
  motion : Fin size → I → t.Carrier ≃ₜ t.Carrier
  small : Fin size → Set t.Carrier
  disjoint : Pairwise (fun k l ↦ Disjoint (window k) (window l))
  continuous : ∀ k, Continuous (fun z : I × t.Carrier ↦ motion k z.1 z.2)
  inverse_continuous : ∀ k, Continuous (fun z : I × t.Carrier ↦ (motion k z.1).symm z.2)
  zero : ∀ k x, motion k 0 x = x
  piecewiseAffine : ∀ k u i j, (t.charts i).symm.trans
    ((motion k u).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3
  region : ∀ k u, (motion k u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  frontier_fixed : ∀ k u, EqOn (motion k u) id (frontier (t.projection ⁻¹' R))
  outside : ∀ k u, EqOn (motion k u) id
    ((step.projection ∘ step.inclusion) ⁻¹' window k)ᶜ
  compact : ∀ k, IsCompact (small k)
  small_window : ∀ k, small k ⊆ (step.projection ∘ step.inclusion) ⁻¹' window k
  source_fixed : ∀ k u, EqOn (motion k u) id (D.endpoint '' K.space \ small k)
  cover : D.exceptionalDoubleValues ⊆ ⋃ k, (step.projection ∘ step.inclusion) '' small k
  crossings : ∀ k, ∀ x y : K.space, x ≠ y →
    (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint x)) =
      (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint y)) →
    (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint x)) ∈
      (step.projection ∘ step.inclusion) '' (small k ∪ motion k 1 '' small k) →
    ∃ B : ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
      (motion k 1 ∘ D.endpoint) K.space (s.projection ⁻¹' R) x y,
      B.chart.source ⊆ window k

theorem OriginalRelativeNormalization.nonempty_finite_annulus_repairs
    (D : OriginalRelativeNormalization step K j R Rim)
    (hK : K.faces.Finite) (hKs : K.space = ProtectedAnnulus.source)
    (hcard : ∀ q ∈ K.faces, q.card ≤ 3) : Nonempty (FiniteAnnulusRepairs D) := by
  classical
  obtain ⟨n, q, _w, W, hW, hdis, _, _, _⟩ := D.exists_exception_schedule
  have hpairs (k : Fin n) : ∃ a b : K.space,
      a ≠ b ∧ D.projected a = (q k : s.Carrier) ∧
        D.projected b = (q k : s.Carrier) := by
    obtain ⟨a, b, hab, ha, hb, _, _⟩ := (hW k).2.2.2.2.2
    exact ⟨a, b, hab, ha, hb⟩
  choose a b hab ha hb using hpairs
  have hN (k : Fin n) : Nonempty (AnnulusBranchMotion D (a k) (b k) (W k) 1) :=
    D.nonempty_annulus_branch_motion hK hKs (a k) (b k) (hab k)
      ((ha k).trans (hb k).symm) (hW k).1 ((ha k).symm ▸ (hW k).2.1) 1 zero_lt_one
  let N (k : Fin n) := Classical.choice (hN k)
  have hsingle (k : Fin n) : W k ∩ D.exceptionalDoubleValues ⊆ {D.projected (a k)} := by
    intro z hz
    have hmem := (hW k).2.2.2.2.1.subset ⟨hz.2, subset_closure hz.1⟩
    exact hmem.trans (ha k).symm
  have hsmall (k : Fin n) :=
    (N k).exists_crossed_change_support hcard (hW k).1 (hsingle k)
  choose Small hcompact hEnd hSmallW hcenter hfix hcross using hsmall
  refine ⟨{
    size := n
    window := W
    motion := fun k ↦ (N k).ambient
    small := Small
    disjoint := fun k l hkl ↦ (hdis hkl).mono subset_closure subset_closure
    continuous := fun k ↦ (N k).continuous
    inverse_continuous := fun k ↦ (N k).continuous_inverse
    zero := fun k ↦ (N k).zero
    piecewiseAffine := fun k ↦ (N k).ambient_PL
    region := fun k ↦ (N k).region
    frontier_fixed := fun k ↦ (N k).frontier_fixed
    outside := ?_
    compact := hcompact
    small_window := fun k ↦ subset_union_left.trans (hSmallW k)
    source_fixed := hfix
    cover := ?_
    crossings := hcross }⟩
  · intro k u
    exact right_branch_motion_fixed_off_window (N k).window (N k).chart
      (N k).support_target (fun _ hz ↦ ((N k).chart_inside hz).2.2)
      (fun _ hz ↦ ((N k).chart_inside hz).1) ((N k).outside u)
  · intro z hz
    obtain ⟨k, hk⟩ := q.surjective ⟨z, hz⟩
    have hq : (q k : s.Carrier) = z := congrArg Subtype.val hk
    exact mem_iUnion.mpr ⟨k, ((ha k).trans hq) ▸ hcenter k⟩

end Geometry.OriginalPLTower
