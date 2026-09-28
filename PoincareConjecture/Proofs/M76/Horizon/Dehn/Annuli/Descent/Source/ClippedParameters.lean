import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.Parameters
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_clipped_planar_source_parameter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hinj : InjOn f K.space)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (q : OpenPartialHomeomorph K.space V2) (O : Set E) (F : E → V2)
    (hqs : q.source = Subtype.val ⁻¹' O)
    (hqval : ∀ x : K.space, q x = F x) (hF : LocallyPiecewiseAffineOn F O)
    (hfit : ∀ x : K.space, f x ∈ Q.source → x ∈ q.source)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target) :
    ∃ (P : SimplicialComplex ℝ V3) (g : V3 → E) (r : V3 → V2),
      P.faces.Finite ∧ P.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      FinitePiecewiseAffineOn g P.space ∧ MapsTo g P.space K.space ∧
      (∀ z ∈ P.space, f (g z) ∈ Q.source ∧ Q (f (g z)) = z) ∧
      (∀ x ∈ K.space, f x ∈ Q.source → Q (f x) ∈ J.space → g (Q (f x)) = x) ∧
      FinitePiecewiseAffineOn r P.space ∧ InjOn r P.space ∧
      (∀ z, r z = F (g z)) ∧
      ∀ z ∈ P.space, z ∈ interior J.space → r z ∈ interior (r '' P.space) := by
  obtain ⟨P, g, hP, hPs, hg, hgK, hright, hleft⟩ :=
    hf.exists_finite_clipped_chart_inverse K hK hinj Q hQ J hJ hJQ
  let r := F ∘ g
  have hgq {z : V3} (hz : z ∈ P.space) :
      (⟨g z, hgK hz⟩ : K.space) ∈ q.source := hfit _ (hright z hz).1
  have hrPL : FinitePiecewiseAffineOn r P.space := hF.comp_finitePiecewiseAffineOn hg
    (fun _ hz ↦ hqs.subset (hgq hz))
  have hri : InjOn r P.space := by
    intro z hz v hv hrv
    have hqeq : q ⟨g z, hgK hz⟩ = q ⟨g v, hgK hv⟩ := by
      simpa only [r, Function.comp_apply, hqval] using hrv
    have hgeq := congrArg Subtype.val (q.injOn (hgq hz) (hgq hv) hqeq)
    exact (hright z hz).2.symm.trans ((congrArg (Q ∘ f) hgeq).trans (hright v hv).2)
  refine ⟨P, g, r, hP, hPs, hg, hgK, hright, hleft, hrPL, hri, fun _ ↦ rfl, ?_⟩
  intro z hz hzJ
  let V : Set K.space := (fun x : K.space ↦ f x) ⁻¹'
    (Q.source ∩ Q ⁻¹' interior J.space)
  have hV : IsOpen V := (Q.isOpen_inter_preimage isOpen_interior).preimage
    hf.continuousOn.domRestrict
  let U := q '' (V ∩ q.source)
  have hU : IsOpen U := q.isOpen_image_of_subset_source
    (hV.inter q.open_source) inter_subset_right
  have hrzU : r z ∈ U := by
    refine ⟨⟨g z, hgK hz⟩, ⟨?_, hgq hz⟩, hqval _⟩
    refine ⟨(hright z hz).1, ?_⟩
    change Q (f (g z)) ∈ interior J.space
    rw [(hright z hz).2]
    exact hzJ
  have hUr : U ⊆ r '' P.space := by
    rintro u ⟨x, ⟨hxV, _⟩, rfl⟩
    have hxP : Q (f x) ∈ P.space := hPs.symm.subset
      ⟨⟨f x, ⟨mem_image_of_mem f x.property, hxV.1⟩, rfl⟩,
        interior_subset hxV.2⟩
    refine ⟨Q (f x), hxP, ?_⟩
    change F (g (Q (f x))) = q x
    rw [hleft x x.property hxV.1 (interior_subset hxV.2), hqval]
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hrzU) hUr)

end PoincareConjecture.M76.Dehn
