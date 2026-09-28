import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.FiberwiseLocalHomeomorph










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_two_covering_phase_adjustments
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d) {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : Bool → SimplicialComplex ℝ E) (hJ : ∀ s, (J s).faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : Bool → E × ℝ → X0)
    (hc : ∀ s, PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-r) r))
    (hi : ∀ s, Topology.IsEmbedding (fun z : (J s).space ×ˢ Icc (-r) r => c s z))
    (hopen : ∀ s, ∀ eps : ℝ, 0 < eps → eps ≤ r →
      IsOpen (c s '' ((J s).space ×ˢ Ioo (-eps) eps)))
    (hdis : Disjoint (c false '' ((J false).space ×ˢ Icc (-r) r))
      (c true '' ((J true).space ×ˢ Icc (-r) r)))
    (theta : Bool → C0) (sigma : Bool → ℝ) (hsigma : ∀ s, sigma s ≠ 0)
    (hproduct : ∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c s (x, 0)))).1,
          theta s + ((sigma s * t : ℝ) : C0)))
    (g : ∀ s, C((J s).space, C0 × C0)) (hg : ∀ s, IsCoveringMap (g s))
    (H : ∀ s, (hamiltonZeroCollarTangentialMap phi (J s) hr (c s) (hc s)).Homotopy (g s))
    (hgPL : ∀ s, PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget (J s) (g s) (theta s)) (J s).space) :
    ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧
      A ⊆ (c false '' ((J false).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∪
        (c true '' ((J true).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c s (x, t))) =
          (g s x, theta s + ((sigma s * t : ℝ) : C0))) ∧
      ∀ s, IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c s '' ((J s).space ×ˢ Ioo (-(r / 4)) (r / 4))) := by
  obtain ⟨psi0, A0, hA0, hA0sub, hpsi0, ⟨H0'⟩, ⟨F0⟩, _, hnormal0, hfixed0, hnew0, _, _⟩ :=
    hphi.exists_hamiltonZero_covering_phase_adjustment hd F (J false) (hJ false) hr
      (c false) (hc false) (hi false) (hopen false) (theta false) (sigma false) (hsigma false)
      (hproduct false) (g false) (hg false) (H false) (hgPL false)
  have hsmall (s : Bool) : (J s).space ×ˢ Ioo (-(r / 2)) (r / 2) ⊆
      (J s).space ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have havoid0 (z : E × ℝ) (hz : z ∈ (J true).space ×ˢ Icc (-r) r) : c true z ∉ A0 := by
    intro h
    exact disjoint_left.mp hdis (image_mono (hsmall false) (hA0sub h)) (mem_image_of_mem _ hz)
  have hsame0 (z : E × ℝ) (hz : z ∈ (J true).space ×ˢ Icc (-r) r) :
      hamiltonZeroAmbientMap psi0 (c true z) = hamiltonZeroAmbientMap phi (c true z) :=
    hfixed0 _ (havoid0 z hz)
  have hmap : hamiltonZeroCollarTangentialMap psi0 (J true) hr (c true) (hc true) =
      hamiltonZeroCollarTangentialMap phi (J true) hr (c true) (hc true) := by
    apply ContinuousMap.ext
    intro x
    change (Q0 (hamiltonZeroAmbientMap psi0 (c true (x, 0)))).1 = _
    rw [hsame0 _ ⟨x.property, by constructor <;> linarith⟩]
    rfl
  have hprod1 (x : (J true).space) (t : ℝ) (ht : t ∈ Icc (-r) r) :
      Q0 (hamiltonZeroAmbientMap psi0 (c true (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap psi0 (c true (x, 0)))).1,
          theta true + ((sigma true * t : ℝ) : C0)) := by
    rw [hsame0 _ ⟨x.property, ht⟩, hsame0 _ ⟨x.property, by constructor <;> linarith⟩]
    exact hproduct true x t ht
  have H1 : (hamiltonZeroCollarTangentialMap psi0 (J true) hr (c true) (hc true)).Homotopy (g true) :=
    hmap.symm ▸ H true
  obtain ⟨psi, A1, hA1, hA1sub, hpsi, ⟨H1'⟩, Fpsi, _, hnormal1, hfixed1, hnew1, _, _⟩ :=
    hpsi0.exists_hamiltonZero_covering_phase_adjustment hd F0 (J true) (hJ true) hr
      (c true) (hc true) (hi true) (hopen true) (theta true) (sigma true) (hsigma true)
      hprod1 (g true) (hg true) H1 (hgPL true)
  have havoid1 (z : E × ℝ) (hz : z ∈ (J false).space ×ˢ Icc (-r) r) : c false z ∉ A1 := by
    intro h
    exact disjoint_left.mp hdis (mem_image_of_mem _ hz) (image_mono (hsmall true) (hA1sub h))
  have hquarter (s : Bool) : (J s).space ×ˢ Icc (-(r / 4)) (r / 4) ⊆
      (J s).space ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hnew (s : Bool) (x : (J s).space) (t : ℝ) (ht : t ∈ Icc (-(r / 4)) (r / 4)) :
      Q0 (hamiltonZeroAmbientMap psi (c s (x, t))) =
        (g s x, theta s + ((sigma s * t : ℝ) : C0)) := by
    cases s with
    | false =>
      rw [hfixed1 _ (havoid1 _ (hquarter false ⟨x.property, ht⟩))]
      exact hnew0 x t ht
    | true => exact hnew1 x t ht
  refine ⟨psi, A0 ∪ A1, hA0.union hA1, union_subset_union hA0sub hA1sub,
    hpsi, ⟨H0'.trans H1'⟩, Fpsi, hnormal1.trans hnormal0, ?_, hnew, ?_⟩
  · intro x hx
    exact (hfixed1 x (fun h => hx (Or.inr h))).trans (hfixed0 x (fun h => hx (Or.inl h)))
  · intro s
    exact hamiltonZeroAmbientMap_isLocalHomeomorphOn_of_fiberwise_covering psi (c s)
      ((hi s).comp (Topology.IsEmbedding.inclusion (hquarter s)))
      (hopen s (r / 4) (by positivity) (by linarith)) (g s) (hg s) (theta s) (hsigma s) (hnew s)

end PoincareConjecture.M76
