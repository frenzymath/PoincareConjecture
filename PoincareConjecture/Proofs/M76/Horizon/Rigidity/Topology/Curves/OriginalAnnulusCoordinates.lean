import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.FinitePLEssentialCircle
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finitePL_original_carrier_coordinates
    {E V G X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {A : Set E} {B : Set X} (H : A ≃ₜ B)
    (F : E → X) (hF : PolyhedralPLInCharts e F A)
    (hFval : ∀ x : A, F x = (H x : X))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (gamma : C(K.space, B))
    (g : G → X) (hg : PolyhedralPLInCharts e g K.space)
    (hgval : ∀ x : K.space, g x = (gamma x : X)) :
    ∃ q : G → E, FinitePiecewiseAffineOn q K.space ∧
      ∀ x : K.space, q x = (H.symm (gamma x) : E) := by
  classical
  let q : G → E := fun z => if hz : z ∈ K.space then
    (H.symm (gamma ⟨z, hz⟩) : E) else 0
  have hqval (x : K.space) : q x = (H.symm (gamma x) : E) := by
    simp only [q, dif_pos x.property]
  have hq : ContinuousOn q K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (H.symm.continuous.comp gamma.continuous)).congr
      (fun x => (hqval x).symm)
  have hmap : MapsTo q K.space A := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (H.symm (gamma ⟨x, hx⟩)).property
  have hinj : InjOn F A := by
    intro x hx y hy heq
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [← hFval] using heq
    exact congrArg Subtype.val (H.injective he)
  have hcomp : PolyhedralPLInCharts e (F ∘ q) K.space := hg.congr (by
    intro x hx
    change g x = F (q x)
    rw [hqval ⟨x, hx⟩, hFval, H.apply_symm_apply]
    exact hgval ⟨x, hx⟩)
  exact ⟨q, hF.finitePiecewiseAffineOn_lift hcompat hinj K hK hq hmap hcomp, hqval⟩

end PoincareConjecture.M76

namespace PoincareConjecture.M76.Dehn

open Metric PLAnnularStrip
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))





theorem exists_originalPL_annulus_core_homotopy
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B : Set X} (H : Ann ≃ₜ B)
    (F : (ℝ × ℝ) → X) (hF : PolyhedralPLInCharts e F Ann)
    (hFval : ∀ x : Ann, F x = (H x : X))
    (gamma : C(Q2, B)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hdepth : ∀ x : Q2, -1 < depth 8 (H.symm (gamma x) : ℝ × ℝ) ∧
      depth 8 (H.symm (gamma x) : ℝ × ℝ) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ q : Q2 ≃ₜ Circle,
      Nonempty (gamma.Homotopy
        ((⟨H, H.continuous⟩ : C(Ann, B)).comp
          (annulusCoreCircle.comp ⟨q, q.continuous⟩))) := by
  let K := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hK : K.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hKs : K.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let T : K.space ≃ₜ Q2 := Homeomorph.setCongr hKs
  let gammaK : C(K.space, B) := gamma.comp ⟨T, T.continuous⟩
  obtain ⟨f, hf, hfv⟩ := exists_finitePL_original_carrier_coordinates e hcompat H F hF hFval
    K hK gammaK g (hKs.symm ▸ hg) (fun x => hgval (T x))
  let delta : C(Q2, Ann) := ⟨fun x => H.symm (gamma x), H.symm.continuous.comp gamma.continuous⟩
  have hvalue (x : Q2) : f x = (delta x : ℝ × ℝ) := hfv (T.symm x)
  have hdelta : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map delta.continuous)) ≠ 1 := by
    have hi := FundamentalGroup.map_injective_of_leftInverse
      (⟨H.symm, H.symm.continuous⟩ : C(B, Ann)) ⟨H, H.continuous⟩
      H.apply_symm_apply (gamma squareRimBase)
    intro hn
    apply hessential
    apply hi
    rw [map_one]
    exact hn
  obtain ⟨q, ⟨G⟩⟩ := exists_finitePL_essential_annulus_core_homotopy delta
    (H.symm.injective.comp hinj) f (hKs ▸ hf) hvalue hdepth hdelta
  refine ⟨q, ⟨{
    toFun := fun z => H (G z)
    continuous_toFun := H.continuous.comp G.continuous
    map_zero_left := ?_
    map_one_left := fun x => congrArg H (G.apply_one x)
  }⟩⟩
  intro x
  rw [G.apply_zero]
  exact H.apply_symm_apply (gamma x)

end PoincareConjecture.M76.Dehn
