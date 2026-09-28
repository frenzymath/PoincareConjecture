import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.TorusTranslation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentPL



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)
local notation "I" => unitInterval

theorem SourceSquareMap.exists_finitePL_translation_track
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (hK : K.faces.Finite) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z)) (v : P2) :
    ∃ (G : I → K.space ≃ₜ K.space) (track : ℝ × E → E),
      Continuous (fun z : I × K.space => G z.1 z.2) ∧
      Continuous (fun z : I × K.space => (G z.1).symm z.2) ∧
      G 0 = Homeomorph.refl K.space ∧
      FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
      (∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (G t x : E)) ∧
      ∀ t : I, ∀ x : K.space,
        H (G t x) = h (h.symm (H x) + (((t : ℝ) * v.1 : AddCircle p),
          ((t : ℝ) * v.2 : AddCircle p))) := by
  classical
  let k₀ := H.trans h.symm
  let G (t : I) : K.space ≃ₜ K.space :=
    (k₀.trans (Homeomorph.addRight
      ((((t : ℝ) * v.1 : ℝ) : AddCircle p), (((t : ℝ) * v.2 : ℝ) : AddCircle p)))).trans k₀.symm
  have hGc : Continuous (fun z : I × K.space => G z.1 z.2) := by
    change Continuous (fun z : I × K.space => k₀.symm (k₀ z.2 +
      ((((z.1 : ℝ) * v.1 : ℝ) : AddCircle p), (((z.1 : ℝ) * v.2 : ℝ) : AddCircle p))))
    fun_prop
  have hGci : Continuous (fun z : I × K.space => (G z.1).symm z.2) := by
    change Continuous (fun z : I × K.space => k₀.symm (k₀ z.2 -
      ((((z.1 : ℝ) * v.1 : ℝ) : AddCircle p), (((z.1 : ℝ) * v.2 : ℝ) : AddCircle p))))
    fun_prop
  have hG0 : G 0 = Homeomorph.refl K.space := by
    apply Homeomorph.ext
    intro x
    change k₀.symm (k₀ x + (((0 * v.1 : ℝ) : AddCircle p), ((0 * v.2 : ℝ) : AddCircle p))) = x
    simp only [zero_mul, AddCircle.coe_zero]
    change k₀.symm (k₀ x + 0) = x
    simp
  let k (x : E) := if hx : x ∈ K.space then k₀ ⟨x, hx⟩ else 0
  have hkval (x : K.space) : k x = k₀ x := by simp only [k, dif_pos x.property]
  have hk : ContinuousOn k K.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact k₀.continuous.congr (fun x => (hkval x).symm)
  let delta : (ℝ × E) →L[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ ℝ E).smulRight v
  let track (z : ℝ × E) : E := k₀.symm
    (k z.2 + (((delta z).1 : AddCircle p), ((delta z).2 : AddCircle p)))
  obtain ⟨J, hJ, hJs⟩ := exists_finite_interval_cylinder K hK (show (0 : ℝ) < 1 by norm_num)
  have hkJ : ContinuousOn (fun z : ℝ × E => k z.2) J.space :=
    hk.comp continuous_snd.continuousOn (fun _ hz => (hJs.subset hz).2)
  have hbasePL : PolyhedralPLInCharts e (fun z : ℝ × E => (h (k z.2) : X)) J.space := by
    have hcomp := hF.comp_finitePiecewiseAffineOn J hJ
      ((J.affineOnFaces_affine (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap).finitePiecewiseAffineOn hJ)
      (fun _ hz => (hJs.subset hz).2)
    apply hcomp.congr
    intro z hz
    change F z.2 = (h (k z.2) : X)
    rw [hkval ⟨z.2, (hJs.subset hz).2⟩]
    exact (hFval ⟨z.2, (hJs.subset hz).2⟩).trans
      (congrArg Subtype.val (h.apply_symm_apply _)).symm
  have htransPL := M.polyhedralPL_torus_translation hcompat H F hF hFval h hvalue J hJ
    (fun z : ℝ × E => k z.2) hkJ hbasePL delta
    ((J.affineOnFaces_affine delta.toContinuousAffineMap).finitePiecewiseAffineOn hJ)
  have htrackc : ContinuousOn track J.space :=
    continuous_subtype_val.comp_continuousOn (k₀.symm.continuous.comp_continuousOn
      (hkJ.add (((AddCircle.continuous_mk' p).comp delta.continuous.fst).continuousOn.prodMk
        ((AddCircle.continuous_mk' p).comp delta.continuous.snd).continuousOn)))
  have htrackPL : FinitePiecewiseAffineOn track J.space := by
    have hFi : InjOn F K.space := by
      intro x hx y hy heq
      have hxy : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
        ((hFval ⟨x, hx⟩).symm.trans (heq.trans (hFval ⟨y, hy⟩)))
      exact congrArg Subtype.val (H.injective hxy)
    apply hF.finitePiecewiseAffineOn_lift hcompat hFi J hJ htrackc
      (fun z _ => (k₀.symm _).property)
    apply htransPL.congr
    intro z _
    change (h _ : X) = F (k₀.symm _)
    rw [hFval]
    exact (congrArg Subtype.val (H.apply_symm_apply _)).symm
  refine ⟨G, track, hGc, hGci, hG0, hJs ▸ htrackPL, ?_, ?_⟩
  · intro t x
    change (k₀.symm (k x + _ ) : E) = _
    rw [hkval]
    rfl
  · intro t x
    exact H.apply_symm_apply _

end PoincareConjecture.M76.PeriodicSquare
