import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.SupportedBall

/-!
# Original-chart PL selection for third-coordinate arc clamping

The endpoint selects the original map or one of two literal affine phase
retractions. Near every point one of the distinct endpoint branches is absent,
so binary finite PL selection supplies its original target-chart certificate.
-/

set_option autoImplicit false
open Set Metric Geometry
open scoped Topology

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem hamiltonZeroTargetThirdPhaseRetraction_eq_of_coe_eq
    {a b : ℝ} (hab : (a : C0) = (b : C0)) :
    hamiltonZeroTargetThirdPhaseRetraction a = hamiltonZeroTargetThirdPhaseRetraction b := by
  apply ContinuousMap.ext
  intro x
  apply (Q0).injective
  simp only [hamiltonZeroTargetThirdPhaseRetraction_coordinates, hab]

theorem hamiltonZeroTargetThirdPhaseRetraction_phase (theta : ℝ) (x : X0) :
    (Q0 (hamiltonZeroTargetThirdPhaseRetraction theta x)).1.1 = (theta : C0) := by
  rw [hamiltonZeroTargetThirdPhaseRetraction_coordinates]

private theorem selection_coordinates_of_missing_branch
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f₀ f₁ f₂ g : E → X0}
    (h₀ : PolyhedralPLInCharts d f₀ K.space) (h₁ : PolyhedralPLInCharts d f₁ K.space)
    (h₂ : ContinuousOn f₂ K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ y ∈ K.space, g y = f₀ y ∨ g y = f₁ y ∨ g y = f₂ y)
    (x : K.space) (hx : g x ≠ f₂ x) :
    ∃ (i : β) (J : SimplicialComplex ℝ E) (W : Set K.space),
      J.faces.Finite ∧ J.space ⊆ K.space ∧ IsOpen W ∧ x ∈ W ∧
      Subtype.val '' W ⊆ J.space ∧ MapsTo g J.space (d i).source ∧
      FinitePiecewiseAffineOn ((d i) ∘ g) J.space := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let U : Set K.space := {z | g z ≠ f₂ z}
  have hU : IsOpen U := (isClosed_eq hg.domRestrict h₂.domRestrict).isOpen_compl
  obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNU⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hU hx
  have hlocal : PolyhedralPLInCharts d g N.space :=
    (h₀.restrict_finite N hN hNK).continuous_selection hd.domain.cover hd.domain.compatible
      N hN (h₁.restrict_finite N hN hNK) (hg.mono hNK) (by
        intro y hy
        rcases hselect y (hNK hy) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact ((hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)) h).elim)
  have hxN : (x : E) ∈ N.space := hVN ⟨x, hxV, rfl⟩
  obtain ⟨i, J, W, hJ, hJN, hW, hxW, hWJ, htarget, hformula⟩ := hlocal.coordinates ⟨x, hxN⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxN⟩ : N.space) ∈ Subtype.val ⁻¹' O
    rw [hOW]
    exact hxW
  refine ⟨i, J, V ∩ (Subtype.val : K.space → E) ⁻¹' O,
    hJ, hJN.trans hNK, hV.inter (hO.preimage continuous_subtype_val),
    ⟨hxV, hxO⟩, ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzN : (z : E) ∈ N.space := hVN ⟨z, hz.1, rfl⟩
  have hzW : (⟨z, hzN⟩ : N.space) ∈ W := by
    rw [← hOW]
    exact hz.2
  exact hWJ ⟨⟨z, hzN⟩, hzW, rfl⟩

/-- Any continuous selection of the original target map and its two literal
phase retractions is PL on the whole finite carrier. -/
theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroThirdPhaseSelection
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (a b : ℝ) (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {Y g : E → X0} (hY : PolyhedralPLInCharts d Y K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ x ∈ K.space, g x = Y x ∨
      g x = hamiltonZeroTargetThirdPhaseRetraction a (Y x) ∨ g x = hamiltonZeroTargetThirdPhaseRetraction b (Y x)) :
    PolyhedralPLInCharts d g K.space := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have ha := hd.polyhedralPL_hamiltonZeroTargetThirdPhaseRetraction a hY
  have hb := hd.polyhedralPL_hamiltonZeroTargetThirdPhaseRetraction b hY
  by_cases hab : (a : C0) = (b : C0)
  · apply hY.continuous_selection hd.domain.cover hd.domain.compatible K hK ha hg
    intro x hx
    rcases hselect x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by rw [hamiltonZeroTargetThirdPhaseRetraction_eq_of_coe_eq hab]; exact h)
  · refine ⟨hg, ?_⟩
    intro x
    by_cases hx : g x = hamiltonZeroTargetThirdPhaseRetraction b (Y x)
    · have hx' : g x ≠ hamiltonZeroTargetThirdPhaseRetraction a (Y x) := by
        intro he
        have hh := congrArg (fun z : X0 => (Q0 z).1.1) (he.symm.trans hx)
        exact hab (by simpa only [hamiltonZeroTargetThirdPhaseRetraction_phase] using hh)
      exact selection_coordinates_of_missing_branch hd K hK hY hb ha.continuousOn hg
        (fun y hy => by
          rcases hselect y hy with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)) x hx'
    · exact selection_coordinates_of_missing_branch hd K hK hY ha hb.continuousOn hg hselect x hx

/-- A continuous arc-clamped ambient endpoint is PL in the unchanged atlases. -/
theorem ChartwisePLMap.hamiltonZero_third_phase_selection {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (a b : ℝ) (g : C(X0, X0))
    (hselect : ∀ x, g x = hamiltonZeroAmbientMap phi x ∨
      g x = hamiltonZeroTargetThirdPhaseRetraction a (hamiltonZeroAmbientMap phi x) ∨
      g x = hamiltonZeroTargetThirdPhaseRetraction b (hamiltonZeroAmbientMap phi x)) :
    ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain g) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hempty : ChartwisePLOn e d (hamiltonZeroAmbientMapInDomain g) ∅ :=
    hphi.congr_mono isOpen_empty (empty_subset _) (fun _ hx => hx.elim)
  apply chartwisePLMap_of_open_and_embedded_parameters (E := V3) e d
    (hamiltonZeroAmbientMapInDomain g) hempty
  intro x _
  obtain ⟨i, j, K, V, f, hK, hV, hxV, _, hVi, hVK, hKt, _, _, _⟩ :=
    hphi.coordinates x (mem_univ x)
  let q : V3 → R0 := fun z =>
    ⟨(e i).symm z, hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _)⟩
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      ((e i).symm.continuousOn.mono hKt)
  have hi : Topology.IsEmbedding (fun z : K.space => (e i).symm z) :=
    (e i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun z : K.space => q z) :=
    hi.codRestrict R0 (fun _ => hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _))
  have hxK : e i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  let z : K.space := ⟨e i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((e i).left_inv (hVi hxV))
  have hVrange : V ⊆ range (fun z : K.space => q z) := by
    intro y hy
    exact ⟨⟨e i y, hVK ⟨y, hy, rfl⟩⟩, Subtype.ext ((e i).left_inv (hVi hy))⟩
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X0)) K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK) i hKt
  have hY := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hqPL
  have hg : PolyhedralPLInCharts d (fun z => g (q z)) K.space :=
    hd.polyhedralPL_hamiltonZeroThirdPhaseSelection a b K hK hY
      (g.continuous.comp_continuousOn hqPL.continuousOn) (fun _ _ => hselect _)
  exact ⟨K, q, z, hK, hq, hiq, hqz,
    Filter.mem_of_superset (hV.mem_nhds hxV) hVrange, hqPL, hg⟩

end PoincareMT.M76
