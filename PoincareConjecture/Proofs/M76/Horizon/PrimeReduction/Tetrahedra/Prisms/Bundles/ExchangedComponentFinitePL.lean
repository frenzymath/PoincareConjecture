import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointInterpolationFinitePL
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiberQuotient
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointComponentAlternatives
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteCarrierComponents



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finitePL_exchanged_prism_component
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A B : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (p : (⋃ i, prismEnds (H i) : Set E)) (hp : τ p ∉ connectedComponent p) :
    ∃ V : (connectedComponentIn (⋃ i, prismEnds (H i)) (p : E) ×ˢ I : Set (E × ℝ)) ≃ₜ
        connectedComponentIn (⋃ i, B i) (p : E),
      V.IsFinitePL ∧
      ∀ z, (V z : E) = prismEndpointFiberMap H L
        (⟨(z : E × ℝ).1,connectedComponentIn_subset _ _ z.property.1⟩,
          ⟨(z : E × ℝ).2,z.property.2⟩) := by
  classical
  have hA (i : ι) : IsCompact (A i) := by
    obtain ⟨u,hu,_⟩ := hH i
    have hc := hu.isCompact
    have heq : Prod.fst '' (A i ×ˢ I : Set (E × ℝ)) = A i := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy.1
      · intro hx; exact ⟨(x,0),⟨hx,by norm_num⟩,rfl⟩
    exact heq ▸ hc.image continuous_fst
  obtain ⟨W,hWval,hW⟩ := exists_twisted_interval_homeomorph_of_prism_interpolation
    H hA L hL hpair τ hτ hτends
  obtain ⟨V,hV⟩ := exists_endpoint_exchanged_component_product H hH τ hτ W hW p hp
  let Ends := (⋃ i, prismEnds (H i) : Set E)
  let T := connectedComponentIn Ends (p : E)
  let J : connectedComponent p ≃ₜ T := subtypeConnectedComponentHomeomorph p
  let V' := (Homeomorph.Set.prod T I).trans
    ((J.symm.prodCongr (Homeomorph.refl I)).trans V)
  have hJval (x : T) : ((J.symm x).val : E) = x := by
    exact congrArg Subtype.val (J.apply_symm_apply x)
  have hV' (z : (T ×ˢ I : Set (E × ℝ))) : (V' z : E) =
      prismEndpointFiberMap H L
        (⟨(z : E × ℝ).1,connectedComponentIn_subset _ _ z.property.1⟩,
          ⟨(z : E × ℝ).2,z.property.2⟩) := by
    change (V (J.symm ⟨(z : E × ℝ).1,z.property.1⟩,⟨(z : E × ℝ).2,z.property.2⟩) : E) = _
    rw [hV,hWval]
    have hpoint : (J.symm ⟨(z : E × ℝ).1,z.property.1⟩).val =
        (⟨(z : E × ℝ).1,connectedComponentIn_subset _ _ z.property.1⟩ : Ends) :=
      Subtype.ext (hJval ⟨(z : E × ℝ).1,z.property.1⟩)
    rw [hpoint]
  obtain ⟨f,hf,hfval⟩ := exists_finitePL_prism_endpoint_interpolation H hH L hL
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_endpoint_triangulation H hH
  obtain ⟨C,hC,hCs⟩ := exists_finite_triangulation_connectedComponentIn K hK (p : E)
  have hCT : C.space = T := by simpa only [hKs] using hCs
  obtain ⟨_,_,_,_,_,_,⟨_,⟨N,hN,hNs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨M,hM,hMs,_⟩ := C.exists_finite_triangulation_prod N hC hN
  have hMT : M.space = T ×ˢ I := hMs.trans (by rw [hCT,hNs])
  have hMf : FinitePiecewiseAffineOn f (T ×ˢ I) := hMT ▸ hf.restrict M hM
    (hMT.subset.trans (prod_mono (connectedComponentIn_subset Ends (p : E)) subset_rfl))
  refine ⟨V',⟨f,hMf,?_⟩,hV'⟩
  intro z
  exact (hV' z).trans (hfval _ _).symm

end PoincareConjecture.M76.PrismBelt
