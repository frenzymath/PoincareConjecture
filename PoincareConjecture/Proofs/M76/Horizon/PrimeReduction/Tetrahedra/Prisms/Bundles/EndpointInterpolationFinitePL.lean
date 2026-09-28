import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberMap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiniteTopology
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem finitePL_prism_endpoint_interpolation_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL)
    (b : Bool) (f : E × ℝ → E)
    (hf : ∀ (a : A) (t : I), f (prismEndMap H a b,t) =
      H ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩) :
    FinitePiecewiseAffineOn f ((range fun a : A => (prismEndMap H a b : E)) ×ˢ I) := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_end_triangulation H hH b
  obtain ⟨v,hv,hvval⟩ := hH.symm
  obtain ⟨u,hu,huval⟩ := hH
  have hKB : K.space ⊆ B := by
    rintro x hx
    obtain ⟨a,rfl⟩ := hKs.subset hx
    exact (prismEndMap H a b).property
  have hvK : FinitePiecewiseAffineOn v (range fun a : A => (prismEndMap H a b : E)) :=
    hKs ▸ hv.restrict K hK hKB
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J,hJ,hJs,J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let first : (E × ℝ) × ℝ →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.comp
      (ContinuousLinearMap.fst ℝ (E × ℝ) ℝ).toContinuousAffineMap
  let time : (E × ℝ) × ℝ →ᴬ[ℝ] ℝ :=
    if b then ContinuousAffineMap.const ℝ _ 1 -
      (ContinuousLinearMap.snd ℝ (E × ℝ) ℝ).toContinuousAffineMap
    else (ContinuousLinearMap.snd ℝ (E × ℝ) ℝ).toContinuousAffineMap
  let step := first.prod time
  have hstep : FinitePiecewiseAffineOn (step ∘ Prod.map v id)
      ((range fun a : A => (prismEndMap H a b : E)) ×ˢ I) :=
    (hvK.prodMap hid).postcomp step
  have hvalue (a : A) (t : I) :
      (step ∘ Prod.map v id) (prismEndMap H a b,t) = ((a : E),(fiberFlip b t : ℝ)) := by
    have hvp : v (prismEndMap H a b) = ((a : E),if b then (1 : ℝ) else 0) := by
      simpa only [prismEndMap,H.symm_apply_apply] using (hvval (prismEndMap H a b)).symm
    cases b <;> simp [Function.comp_def,step,first,time,hvp,fiberFlip,unitInterval.symm]
  have hmap : MapsTo (step ∘ Prod.map v id)
      ((range fun a : A => (prismEndMap H a b : E)) ×ˢ I) (A ×ˢ I) := by
    rintro ⟨x,t⟩ ⟨⟨a,rfl⟩,ht⟩
    rw [hvalue a ⟨t,ht⟩]
    exact ⟨a.property,(fiberFlip b ⟨t,ht⟩).property⟩
  apply (hu.comp hstep hmap).congr
  rintro ⟨x,t⟩ ⟨⟨a,rfl⟩,ht⟩
  change u ((step ∘ Prod.map v id) (prismEndMap H a b,t)) = f (prismEndMap H a b,t)
  rw [hvalue a ⟨t,ht⟩,hf a ⟨t,ht⟩]
  exact (huval ⟨(a,fiberFlip b ⟨t,ht⟩),a.property,(fiberFlip b ⟨t,ht⟩).property⟩).symm

theorem exists_finitePL_prism_endpoint_interpolation
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A B : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t) :
    ∃ f : E × ℝ → E,
      FinitePiecewiseAffineOn f ((⋃ i, prismEnds (H i)) ×ˢ I) ∧
      ∀ (p : (⋃ i, prismEnds (H i) : Set E)) (t : I),
        f (p,t) = prismEndpointFiberMap H L (p,t) := by
  classical
  let f : E × ℝ → E := fun z =>
    if hz : z ∈ (⋃ i, prismEnds (H i)) ×ˢ I then
      prismEndpointFiberMap H L (⟨z.1,hz.1⟩,⟨z.2,hz.2⟩) else 0
  have hf (p : (⋃ i, prismEnds (H i) : Set E)) (t : I) :
      f (p,t) = prismEndpointFiberMap H L (p,t) := by
    simp only [f,dif_pos (show ((p : E),(t : ℝ)) ∈ (⋃ i, prismEnds (H i)) ×ˢ I from
      ⟨p.property,t.property⟩)]
  have hpieces (z : ι × Bool) : FinitePiecewiseAffineOn f
      ((range fun a : A z.1 => (prismEndMap (H z.1) a z.2 : E)) ×ˢ I) := by
    apply finitePL_prism_endpoint_interpolation_piece (H z.1) (hH z.1) z.2 f
    intro a t
    exact (hf (prismEndpointLift H z.1 a z.2) t).trans
      (prismEndpointFiberMap_apply H L hL z.1 a z.2 t)
  have hcover : (⋃ z : ι × Bool,
      (range fun a : A z.1 => (prismEndMap (H z.1) a z.2 : E)) ×ˢ I) =
        (⋃ i, prismEnds (H i)) ×ˢ I := by
    ext ⟨x,t⟩
    simp only [mem_iUnion,mem_prod,mem_range,prismEnds]
    constructor
    · rintro ⟨⟨i,b⟩,⟨a,ha⟩,ht⟩
      exact ⟨⟨i,⟨a,b⟩,ha⟩,ht⟩
    · rintro ⟨⟨i,⟨a,b⟩,ha⟩,ht⟩
      exact ⟨⟨i,b⟩,⟨a,ha⟩,ht⟩
  exact ⟨f,hcover ▸ FinitePiecewiseAffineOn.iUnion hpieces,hf⟩

end PoincareConjecture.M76.PrismBelt
