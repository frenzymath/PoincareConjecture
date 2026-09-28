import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SphereAnnulusProductBalls
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1

theorem ChartwisePLSphere.exists_finitePL_annulus_parameter
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f Annulus)
    (hfi : InjOn f Annulus) (hfS : MapsTo f Annulus S) :
    ∃ (g : P2 → V3) (c : Annulus ≃ₜ (g '' Annulus)),
      FinitePiecewiseAffineOn g Annulus ∧ c.IsFinitePL ∧
      (∀ z : Annulus, (c z : V3) = g z) ∧
      MapsTo g Annulus Sphere ∧
      (∀ z ∈ Annulus, s.map (g z) = f z) ∧
      s.map '' (g '' Annulus) = f '' Annulus := by
  classical
  let g : P2 → V3 := fun x =>
    if hx : x ∈ Annulus then s.parametrization.symm ⟨f x,hfS hx⟩ else 0
  have hgval (x : Annulus) : g x =
      (s.parametrization.symm ⟨f x,hfS x.property⟩ : V3) := by
    simp only [g,dif_pos x.property]
  have hgcont : ContinuousOn g Annulus := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (s.parametrization.symm.continuous.comp
      (hf.continuousOn.domRestrict.subtype_mk (fun x => hfS x.property)))
    convert h using 1
    funext x
    exact hgval x
  have hgS : MapsTo g Annulus Sphere := by
    intro x hx
    rw [hgval ⟨x,hx⟩]
    exact (s.parametrization.symm ⟨f x,hfS hx⟩).property
  have hvalue (x : P2) (hx : x ∈ Annulus) : s.map (g x) = f x := by
    rw [hgval ⟨x,hx⟩,s.map_eq,s.parametrization.apply_symm_apply]
  have hsinj : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  obtain ⟨_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := exists_square_product_band_annulus
  have hcomp : PolyhedralPLInCharts e (s.map ∘ g) Annulus :=
    hf.congr (fun x hx => (hvalue x hx).symm)
  have hg : FinitePiecewiseAffineOn g Annulus := by
    rw [← hKs]
    exact s.piecewiseAffine.finitePiecewiseAffineOn_lift hcompat hsinj K hK
      (hgcont.mono hKs.subset) (fun _ hx => hgS (hKs.subset hx)) (hKs.symm ▸ hcomp)
  have hginj : InjOn g Annulus := by
    intro x hx y hy hxy
    apply hfi hx hy
    rw [← hvalue x hx,← hvalue y hy,hxy]
  obtain ⟨c,hc,hcval⟩ := hg.exists_homeomorph_image hginj
  refine ⟨g,c,hg,hc,hcval,hgS,hvalue,?_⟩
  rw [image_image]
  exact image_congr (fun x hx => hvalue x hx)

end PoincareConjecture.M76
