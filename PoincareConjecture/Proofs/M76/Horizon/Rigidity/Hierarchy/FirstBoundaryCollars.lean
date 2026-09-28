import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Collars.DisjointBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.DisjointPhaseCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.PhaseBoundaryGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc










set_option autoImplicit false
open Set Geometry Topology Poincare.Topology

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private theorem image_reverse_collar {E X : Type*} (c : E × ℝ → X)
    (K : Set E) (I : Set ℝ) (hI : ∀ t ∈ I, -t ∈ I) :
    (fun z : E × ℝ => c (z.1, -z.2)) '' (K ×ˢ I) = c '' (K ×ˢ I) := by
  ext x
  constructor
  · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    exact ⟨(z, -t), ⟨hz, hI t ht⟩, rfl⟩
  · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    exact ⟨(z, -t), ⟨hz, hI t ht⟩, by simp⟩



theorem exists_hamiltonZero_first_boundary_collars
    {E : Type*} [TopologicalSpace E]
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {alpha beta : ℝ} (ha : 0 < alpha) (hab : alpha < beta) (hb : beta < p)
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    {rho : ℝ} (hrho : 0 < rho) (c : Bool → E × ℝ → X0)
    (hi : ∀ s, IsEmbedding (fun z : (K s ×ˢ Icc (-rho) rho : Set (E × ℝ)) => c s z))
    (hopen : ∀ s eps, 0 < eps → eps ≤ rho → IsOpen (c s '' (K s ×ˢ Ioo (-eps) eps)))
    (H : ∀ s, K s ≃ₜ
      (hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} : Set X0))
    (hzero : ∀ s (x : K s), c s (x, 0) = H s x)
    (g : ∀ s, C(K s, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (hproduct : ∀ s (x : K s) t, t ∈ Icc (-rho) rho →
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        (g s x, (if s then (beta : C0) else (alpha : C0)) +
          (((if s then -1 else 1) * t : ℝ) : C0)))
    (hfront : ∀ side : Bool,
      frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
        (if side then beta else alpha) (if side then alpha + p else beta)) =
          hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)}) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
      ∀ side : Bool,
        let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p
          (if side then beta else alpha) (if side then alpha + p else beta)
        let B := Sum.inl '' K false ∪ Sum.inr '' K true
        ∃ (collar : (E ⊕ E) × ℝ → X0) (cover : C(B, C0 × C0)),
          IsCompact B ∧ B.Nonempty ∧ ContinuousOn collar (B ×ˢ Icc (-r) r) ∧
          IsEmbedding (fun z : (B ×ˢ Icc (-r) r : Set ((E ⊕ E) × ℝ)) => collar z) ∧
          IsOpen (collar '' (B ×ˢ Ioo (-r) r)) ∧
          collar '' (B ×ˢ ({0} : Set ℝ)) = frontier R ∧
          (∀ z ∈ B ×ˢ Icc (-r) r, collar z ∈ R ↔ 0 ≤ z.2) ∧
          IsCoveringMap cover ∧
          ∀ x : B, ∀ t ∈ Icc (-r) r,
            (Q0 (hamiltonZeroAmbientMap phi (collar (x, t)))).1 = cover x := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hleft (z : E × ℝ) (hz : z ∈ K false ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c false z) = ((alpha + z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct false ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, Bool.false_eq_true, if_false, one_mul,
      Prod.snd, AddCircle.coe_add] using h
  have hright (z : E × ℝ) (hz : z ∈ K true ×ˢ Icc (-rho) rho) :
      hamiltonZeroCircleMap phi (c true z) = ((beta - z.2 : ℝ) : C0) := by
    have h := congrArg Prod.snd (hproduct true ⟨z.1, hz.1⟩ z.2 hz.2)
    simpa only [hamiltonZeroAmbientMap_circle, if_true, neg_one_mul, Prod.snd,
      sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg] using h
  obtain ⟨r, hr, hrrho, hra, hrgap, hrpb, hsub, hdis, hside⟩ :=
    exists_disjoint_inward_phase_collar_radius p (hamiltonZeroCircleMap phi) K c
      hrho ha hab hb hleft hright
  have hne (s : Bool) : (K s).Nonempty := by
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap phi F
      (if s then (beta : C0) else (alpha : C0))
    exact ⟨(H s).symm ⟨x, hx⟩, ((H s).symm ⟨x, hx⟩).property⟩
  have hzimage (s : Bool) : c s '' (K s ×ˢ ({0} : Set ℝ)) =
      hamiltonZeroCircleMap phi ⁻¹' {if s then (beta : C0) else (alpha : C0)} := by
    exact (hamiltonZero_phase_boundary_geometry phi F K
      (fun s => if s then (beta : C0) else (alpha : C0)) H c hzero (hfront false)).2.1 s
  refine ⟨r, hr, hrrho, ?_⟩
  intro side R B
  let c' (s : Bool) (z : E × ℝ) := c s (z.1, if side then -z.2 else z.2)
  have hneg (t : ℝ) (ht : t ∈ Icc (-r) r) : -t ∈ Icc (-r) r := by
    constructor <;> linarith [ht.1, ht.2]
  have htime (t : ℝ) (ht : t ∈ Icc (-r) r) :
      (if side then -t else t) ∈ Icc (-rho) rho := by
    cases side <;> dsimp <;> constructor <;> linarith [ht.1, ht.2]
  have himage (s : Bool) (I : Set ℝ) (hI : ∀ t ∈ I, -t ∈ I) :
      c' s '' (K s ×ˢ I) = c s '' (K s ×ˢ I) := by
    cases side
    · rfl
    · exact image_reverse_collar (c s) (K s) I hI
  have hi' (s : Bool) : IsEmbedding
      (fun z : (K s ×ˢ Icc (-r) r : Set (E × ℝ)) => c' s z) := by
    let flip : (E × ℝ) ≃ₜ (E × ℝ) :=
      { toFun := fun z => (z.1, -z.2)
        invFun := fun z => (z.1, -z.2)
        left_inv := by intro z; simp
        right_inv := by intro z; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    cases side
    · exact (hi s).comp (IsEmbedding.inclusion (hsub s))
    · exact (hi s).comp ((flip.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
        (K s ×ˢ Icc (-rho) rho) (fun z => ⟨z.property.1, htime z.val.2 z.property.2⟩))
  have ho' (s : Bool) : IsOpen (c' s '' (K s ×ˢ Ioo (-r) r)) := by
    rw [himage s _ (by intro t ht; constructor <;> linarith [ht.1, ht.2])]
    exact hopen s r hr hrrho
  have hdis' : Disjoint (c' false '' (K false ×ˢ Icc (-r) r))
      (c' true '' (K true ×ˢ Icc (-r) r)) := by
    rw [himage false _ hneg, himage true _ hneg]
    exact hdis
  have hz' : c' false '' (K false ×ˢ ({0} : Set ℝ)) ∪
      c' true '' (K true ×ˢ ({0} : Set ℝ)) = frontier R := by
    rw [himage false _ (by simp), himage true _ (by simp), hzimage false, hzimage true]
    rw [hfront side]
    ext x
    simp
  have hside' (s : Bool) (z : E × ℝ) (hz : z ∈ K s ×ˢ Icc (-r) r) :
      c' s z ∈ R ↔ 0 ≤ z.2 := by
    cases side
    · exact hside s z hz
    · change hamiltonZeroCircleMap phi (c s (z.1, -z.2)) ∈
        AddCircle.closedIntervalArc p beta (alpha + p) ↔ _
      have ht : -z.2 ∈ Icc (-rho) rho := htime z.2 hz.2
      cases s
      · rw [hleft (z.1, -z.2) ⟨hz.1, ht⟩]
        have heq : ((alpha + -z.2 : ℝ) : C0) = ((alpha + p - z.2 : ℝ) : C0) := by
          rw [show alpha + p - z.2 = (alpha + -z.2) + p by ring, AddCircle.coe_add_period]
        rw [heq, AddCircle.coe_mem_closedIntervalArc_shifted_iff p
          (c := (alpha + beta) / 2) (by linarith) (by linarith)
          (by constructor <;> linarith [hz.2.1, hz.2.2])]
        constructor
        · intro h; linarith [h.2]
        · intro h; constructor <;> linarith [hz.2.1, hz.2.2]
      · rw [hright (z.1, -z.2) ⟨hz.1, ht⟩]
        rw [AddCircle.coe_mem_closedIntervalArc_shifted_iff p
          (c := (alpha + beta) / 2) (by linarith) (by linarith)
          (by constructor <;> linarith [hz.2.1, hz.2.2])]
        constructor
        · intro h; linarith [h.1]
        · intro h; constructor <;> linarith [hz.2.1, hz.2.2]
  have hprod' (s : Bool) (x : K s) (t : ℝ) (ht : t ∈ Icc (-r) r) :
      (Q0 (hamiltonZeroAmbientMap phi (c' s (x, t)))).1 = g s x :=
    congrArg Prod.fst (hproduct s x _ (htime t ht))
  obtain ⟨cover, hB, hBne, hcB, hiB, hoB, hzB, hsB, hgB, hpB⟩ :=
    exists_hamiltonZero_disjoint_boundary_bicollar phi (hK false) (hK true)
      (Or.inl (hne false)) hr (c' false) (c' true) (hi' false) (hi' true) hdis'
      (ho' false) (ho' true) hz' (hside' false) (hside' true)
      (g false) (hg false) (g true) (hg true) (hprod' false) (hprod' true)
  exact ⟨sumBicollarMap (c' false) (c' true), cover, hB, hBne,
    hcB, hiB, hoB, hzB, hsB, hgB, hpB⟩

end PoincareConjecture.M76
