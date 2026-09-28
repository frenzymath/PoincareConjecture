import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.HornOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.Pruning
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.Cover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H)

theorem exists_finite_disjoint_end_cut_cover {ι : Type v} {epsilon delta rho constant h : ℝ}
    (N : ι → TerminalStrongNeck Q.extension delta)
    (horn : ι → StrongHorn Q.extension epsilon)
    (hdelta : delta ≤ 1 / 200) (hhalf : delta < 1 / 2)
    (hornCuts : ∀ i, HornEndCut (horn i) (N i) rho)
    (cuts : ∀ i, SurgeryEndCut ((N i).spatialNeck hhalf))
    (htail : ∀ i, (cuts i).tail = (hornCuts i).carrier)
    (hrho : 0 < rho) (hconstant : 1 ≤ constant) (hh : 0 < h)
    (hhd : h ≤ rho * delta) (hhC : h ≤ rho / (2 * constant))
    (hlevel : ∀ i, (Q.extension.extended.connection T).scalarCurvature (N i).center = h⁻¹ ^ 2)
    (hboundary : ∀ i x, x ∈ (horn i).boundary_sphere →
      (Q.extension.extended.connection T).scalarCurvature x < 32 * constant * rho⁻¹ ^ 2)
    (hcarrier : ∀ i, (N i).carrier ⊆ (horn i).carrier)
    (hcore : ∀ i, (N i).center ∈
      SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho)
    (hhorn : ∀ i, Disjoint (horn i).carrier
      {x | (Q.extension.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2})
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail) :
    ∃ s : Finset ι,
      (s : Set ι).Pairwise (fun i j => Disjoint (N i).carrier (N j).carrier) ∧
      (s : Set ι).Pairwise (fun i j => Disjoint (cuts i).tail (cuts j).tail) ∧
      IsCompact (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \
        ⋃ i ∈ s, (cuts i).tail) ∧
      ∀ K : TerminalComponentPath Q.extension,
        (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
        ∀ e : TerminalEnd K, ∃ i ∈ s, ∃ n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
  classical
  have hcpos : 0 < constant := lt_of_lt_of_le zero_lt_one hconstant
  obtain ⟨selected, hselected, hdis, hmeet⟩ := Q.exists_finite_disjoint_neck_selection
    hhalf (sq_pos_of_pos (inv_pos.mpr hh)) (range N) (by
      rintro P ⟨i, rfl⟩
      simpa only [Q.terminal_scalar_eq] using hlevel i)
  have hindex : ∀ P : selected, ∃ i, N i = P.val :=
    fun P => hselected P.val P.property
  choose index hindex using hindex
  let s : Finset ι := Finset.univ.image index
  have hsneck : (s : Set ι).Pairwise fun i j => Disjoint (N i).carrier (N j).carrier := by
    intro i hi j hj hij
    obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hj
    rw [hindex P, hindex R]
    exact hdis P.property R.property (fun hPR => hij (congrArg index (Subtype.ext hPR)))
  have hscover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i ∈ s, ∃ n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
    intro K hK e
    obtain ⟨i, n, hn⟩ := hcover K hK e
    obtain ⟨P, hP, hiP⟩ := hmeet (N i) (mem_range_self i)
    let j := index ⟨P, hP⟩
    have hj : j ∈ s := Finset.mem_image.mpr ⟨⟨P, hP⟩, Finset.mem_univ _, rfl⟩
    have hij : ((N i).carrier ∩ (N j).carrier).Nonempty := by
      simpa only [j, hindex] using hiP
    obtain ⟨p, hp, hNp⟩ := hcore i
    have hpcomp : p ∈ connectedComponent (N i).center := by
      rw [← connectedComponent_eq hNp]
      exact mem_connectedComponent
    have hpC : p ∉ (cuts i).tail := fun hx =>
      disjoint_left.mp (hornCuts i).disjoint_low_curvature (htail i ▸ hx) hp
    have hpH : p ∉ (horn j).carrier := fun hx => disjoint_left.mp (hhorn j) hx hp
    obtain ⟨m, _, hm⟩ := e.exists_tail_subset_horn_cut_of_overlapping_necks
      (horn j) (N i) (N j) hdelta hhalf (cuts i) (hornCuts j)
      hrho hcpos hh hhd hhC (hlevel i) (hboundary j) (hcarrier j) hij
      hpcomp hpC hpH n hn
    exact ⟨j, hj, m, (htail j).symm ▸ hm⟩
  have hlow : ∀ i ∈ s, Disjoint
      {x | (Q.extension.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2}
      (closure (cuts i).tail) := by
    intro i _
    rw [(cuts i).closure_tail]
    apply disjoint_union_right.mpr
    constructor
    · rw [htail i]
      exact (hornCuts i).disjoint_low_curvature.symm
    · apply disjoint_left.mpr
      intro x hx hsphere
      have hlower := (((N i).spatialNeck hhalf).scalar_within_factor_two_on_carrier
        (Q.extension.extended.connection T) hdelta ((N i).central_sphere_subset hsphere)).1
      change (Q.extension.extended.connection T).scalarCurvature (N i).center / 2 ≤
        (Q.extension.extended.connection T).scalarCurvature x at hlower
      rw [hlevel i] at hlower
      have hbarrier := Surgery.Terminal.linear_boundary_lt_half_height_scalar
        hrho hcpos hh hdelta hhd hhC
      have hmul := mul_le_mul_of_nonneg_right hconstant (sq_nonneg rho⁻¹)
      change (Q.extension.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2 at hx
      nlinarith [sq_pos_of_pos (inv_pos.mpr hrho)]
  obtain ⟨t, hts, httail, htcover, _⟩ := SurgeryEndCut.exists_disjoint_tail_subfamily
    (Q.extension.extended.connection T) rho (fun i => (N i).spatialNeck hhalf)
    cuts s hsneck (fun i _ => hcore i) hlow
  have htend : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i ∈ t, ∃ n, Subtype.val '' e.tail n ⊆ (cuts i).tail := by
    intro K hK e
    obtain ⟨i, hi, n, hn⟩ := hscover K hK e
    obtain ⟨j, hj, hij⟩ := htcover i hi
    exact ⟨j, hj, n, hn.trans hij⟩
  refine ⟨t, fun i hi j hj hij => hsneck (hts hi) (hts hj) hij, httail, ?_, htend⟩
  apply Q.isCompact_core_diff_of_end_tail_cover rho
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => (cuts i).tail_isOpen)
  intro K hK e
  obtain ⟨i, hi, n, hn⟩ := htend K hK e
  exact ⟨n, fun x hx => mem_iUnion₂.mpr ⟨i, hi, hn hx⟩⟩

end PoincareConjecture.SingularLimitConclusion
