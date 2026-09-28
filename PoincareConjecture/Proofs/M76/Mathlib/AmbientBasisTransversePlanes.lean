import PoincareConjecture.Proofs.M76.Mathlib.FramePlaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.TransversePlaneDimension











set_option autoImplicit false

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsSecantTransverse.comap_subtype {K V : Submodule ℝ E} {S : Set V}
    (hK : K.IsSecantTransverse (V.subtype '' S)) :
    (K.comap V.subtype).IsSecantTransverse S := by
  let Q := (ContinuousLinearMap.id ℝ E - K.starProjection).comp V.subtypeL
  have hker : Q.ker = K.comap V.subtype := by
    ext x
    change ((x : E) - K.starProjection (x : E) = 0) ↔ (x : E) ∈ K
    rw [sub_eq_zero, eq_comm, K.starProjection_eq_self_iff]
  obtain ⟨c, hc, hb⟩ := hK
  rw [← hker]
  apply isSecantTransverse_ker_of_lower_bound Q hc
  intro x hx y hy
  rw [← map_sub]
  exact hb (x : E) ⟨x, hx, rfl⟩ (y : E) ⟨y, hy, rfl⟩

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem isRadialEmbedding_iff_isSecantTransverse_ker_subtype
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      Q.ker.IsSecantTransverse (V.subtype '' (A.basisRadialEmbedding b).cone.space) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ := BasisRadialProjection.exists_pos_secant_bound
      (⟨Q.comp V.subtypeL, h⟩ : A.BasisRadialProjection b F)
    apply Submodule.isSecantTransverse_ker_of_lower_bound Q hc
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hb x hx y hy
  · intro h
    apply A.isRadialEmbedding_of_injOn_basisCone b (Q.comp V.subtypeL)
    intro x hx y hy he
    apply Subtype.ext
    exact h.injOn Q rfl ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ he



theorem disjoint_map_faceSpan_of_isSecantTransverse
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) {s : Finset ι} (hs : s ∈ A.faces)
    {K : Submodule ℝ E}
    (hK : K.IsSecantTransverse (V.subtype '' (A.basisRadialEmbedding b).cone.space)) :
    Disjoint ((Submodule.span ℝ (b '' (s : Set ι))).map V.subtype) K := by
  have hd := A.disjoint_faceSpan_of_isSecantTransverse b hs hK.comap_subtype
  apply Submodule.disjoint_def.mpr
  intro x hx hk
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  have hz := Submodule.disjoint_def.mp hd v hv hk
  exact congrArg Subtype.val hz




theorem isRadialEmbedding_iff_injOn_basisCone_subtype
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      InjOn Q (V.subtype '' (A.basisRadialEmbedding b).cone.space) := by
  constructor
  · intro h
    exact ((A.isRadialEmbedding_iff_isSecantTransverse_ker_subtype V b Q).mp h).injOn Q rfl
  · intro h
    apply A.isRadialEmbedding_of_injOn_basisCone b (Q.comp V.subtypeL)
    intro x hx y hy he
    exact Subtype.ext (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ he)




noncomputable def frameAmbientBasisPlaneHomeomorph
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (J : F →L[ℝ] V) (hJ : Function.Injective J) :
    (V.subtypeL.comp J).range.TransverseComplementPlaneSpace
      (V.subtype '' (A.basisRadialEmbedding b).cone.space) ≃ₜ
      {Q : (V.subtypeL.comp J).FrameProjectionSpace //
        A.IsRadialEmbedding (fun i => Q.val (b i))} := by
  let J' : F →L[ℝ] E := V.subtypeL.comp J
  have hJ' : Function.Injective J' := fun x y h => hJ (Subtype.val_injective h)
  refine (J'.frameComplementPlaneHomeomorph hJ').subtype ?_
  intro K
  rw [A.isRadialEmbedding_iff_isSecantTransverse_ker_subtype,
    J'.ker_frameComplementPlaneHomeomorph hJ' K]

end AbstractSimplicialComplex
