import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.FirstBoundaryCollars

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_inward_first_phase_collars
    {E : Type*} [TopologicalSpace E]
    (phi : C(H0, H0)) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hi : ∀ s, IsEmbedding (fun z : K s ×ˢ Icc (-rho) rho => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho → IsOpen (c s '' (K s ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, K s ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (b : C0) else (a : C0)} : Set X0))
    (hzero : ∀ s (x : K s), c s (x, 0) = (H s x : X0))
    (g : ∀ s, C(K s, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (hproduct : ∀ s (x : K s) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        (g s x, (if s then (b : C0) else (a : C0)) +
          (((if s then -1 else 1) * t : ℝ) : C0))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧ ∀ complementary : Bool,
      let l := if complementary then b else a
      let u := if complementary then a + p else b
      let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p l u
      ∃ (K' : Bool → Set E) (c' : Bool → E × ℝ → X0)
        (H' : ∀ s, K' s ≃ₜ
          (hamiltonZeroCircleMap phi ⁻¹' {((if s then u else l : ℝ) : C0)} : Set X0))
        (g' : ∀ s, C(K' s, C0 × C0)),
        (∀ s, IsCompact (K' s)) ∧
        (∀ s, IsEmbedding (fun z : K' s ×ˢ Icc (-r) r => c' s z)) ∧
        (∀ s, IsOpen (c' s '' (K' s ×ˢ Ioo (-r) r))) ∧
        (∀ s, ∀ z ∈ K' s ×ˢ Icc (-r) r, c' s z ∈ R ↔ 0 ≤ z.2) ∧
        (∀ s, ∀ z ∈ K' s ×ˢ Icc (-r) 0, hamiltonZeroCircleMap phi (c' s z) =
          ((if s then u - z.2 else l + z.2 : ℝ) : C0)) ∧
        (∀ s, IsCoveringMap (g' s)) ∧
        (∀ s (z : K' s), c' s (z, 0) = (H' s z : X0)) ∧
        ∀ s (z : K' s), (Q0 (hamiltonZeroAmbientMap phi (c' s (z, 0)))).1 = g' s z := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hleft (z : E × ℝ) (hz : z ∈ K false ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c false z) = ((a + z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct false ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, Bool.false_eq_true, if_false, one_mul,
      Prod.snd, AddCircle.coe_add] using h
  have hright (z : E × ℝ) (hz : z ∈ K true ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c true z) = ((b - z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct true ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, if_true, neg_one_mul, Prod.snd,
      sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg] using h
  obtain ⟨r, hr, hrrho, hra, hrgap, hrpb, hsub, _, hside⟩ :=
    exists_disjoint_inward_phase_collar_radius p (hamiltonZeroCircleMap phi) K c
      hrho ha hab hb hleft hright
  have htime {t : ℝ} (ht : t ∈ Icc (-r) r) : -t ∈ Icc (-rho) rho := by
    constructor <;> linarith [ht.1, ht.2]
  have htangent (s : Bool) (z : K s) :
      (Q0 (hamiltonZeroAmbientMap phi (c s (z, 0)))).1 = g s z :=
    congrArg Prod.fst (hproduct s z 0 ⟨by linarith, hrho.le⟩)
  refine ⟨r, hr, hrrho, ?_⟩
  intro complementary
  cases complementary
  · simp only [Bool.false_eq_true, if_false, apply_ite]
    refine ⟨K, c, (fun s => (H s).trans (Homeomorph.setCongr (by cases s <;> rfl))),
      g, hK, (fun s => (hi s).comp (IsEmbedding.inclusion (hsub s))),
      (fun s => hopen s r hr hrrho), hside, ?_, hg, hzero, htangent⟩
    intro s z hz
    have hz' : z ∈ K s ×ˢ Icc (-rho) rho :=
      hsub s ⟨hz.1, hz.2.1, hz.2.2.trans hr.le⟩
    cases s
    · exact hleft z hz'
    · exact hright z hz'
  · dsimp only [if_true]
    let K' (s : Bool) := K (!s)
    let c' (s : Bool) (z : E × ℝ) := c (!s) (z.1, -z.2)
    let H' (s : Bool) : K' s ≃ₜ
        (hamiltonZeroCircleMap phi ⁻¹' {((if s then a + p else b : ℝ) : C0)} : Set X0) :=
      (H (!s)).trans (Homeomorph.setCongr (by cases s <;> simp))
    let g' (s : Bool) := g (!s)
    let flip : (E × ℝ) ≃ₜ (E × ℝ) :=
      (Homeomorph.refl E).prodCongr (Homeomorph.neg ℝ)
    have hi' (s : Bool) : IsEmbedding (fun z : K' s ×ˢ Icc (-r) r => c' s z) :=
      (hi (!s)).comp ((flip.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
        (K (!s) ×ˢ Icc (-rho) rho) (fun z => ⟨z.property.1, htime z.property.2⟩))
    have himage (s : Bool) : c' s '' (K' s ×ˢ Ioo (-r) r) =
        c (!s) '' (K (!s) ×ˢ Ioo (-r) r) := by
      ext x
      constructor
      · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
        exact ⟨(z, -t), ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩, rfl⟩
      · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
        exact ⟨(z, -t), ⟨hz, by constructor <;> linarith [ht.1, ht.2]⟩, by simp [c']⟩
    have hshift (t : ℝ) : ((a + -t : ℝ) : C0) = ((a + p - t : ℝ) : C0) := by
      rw [show a + p - t = (a + -t) + p by ring, AddCircle.coe_add_period]
    refine ⟨K', c', H', g', (fun s => hK (!s)), hi', ?_, ?_, ?_,
      (fun s => hg (!s)), ?_, ?_⟩
    · intro s
      rw [himage]
      exact hopen (!s) r hr hrrho
    · intro s z hz
      have ht := htime hz.2
      cases s
      · change hamiltonZeroCircleMap phi (c true (z.1, -z.2)) ∈
          AddCircle.closedIntervalArc p b (a + p) ↔ _
        rw [hright (z.1, -z.2) ⟨hz.1, ht⟩,
          AddCircle.coe_mem_closedIntervalArc_shifted_iff p
            (c := (a + b) / 2) (by linarith) (by linarith)
            (by constructor <;> linarith [hz.2.1, hz.2.2])]
        constructor
        · intro h; linarith [h.1]
        · intro h; constructor <;> linarith [hz.2.1, hz.2.2]
      · change hamiltonZeroCircleMap phi (c false (z.1, -z.2)) ∈
          AddCircle.closedIntervalArc p b (a + p) ↔ _
        rw [hleft (z.1, -z.2) ⟨hz.1, ht⟩, hshift,
          AddCircle.coe_mem_closedIntervalArc_shifted_iff p
            (c := (a + b) / 2) (by linarith) (by linarith)
            (by constructor <;> linarith [hz.2.1, hz.2.2])]
        constructor
        · intro h; linarith [h.2]
        · intro h; constructor <;> linarith [hz.2.1, hz.2.2]
    · intro s z hz
      have ht := htime (show z.2 ∈ Icc (-r) r from ⟨hz.2.1, hz.2.2.trans hr.le⟩)
      cases s
      · simpa [c', sub_neg_eq_add] using hright (z.1, -z.2) ⟨hz.1, ht⟩
      · exact (hleft (z.1, -z.2) ⟨hz.1, ht⟩).trans (hshift z.2)
    · intro s z
      change c (!s) (z, -(0 : ℝ)) = (H (!s) z : X0)
      simpa only [neg_zero] using hzero (!s) z
    · intro s z
      simpa [c', g'] using htangent (!s) z

end PoincareConjecture.M76
