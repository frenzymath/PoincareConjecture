import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasSignCover
import PoincareConjecture.Proofs.M76.Wall.ProtectedRegionHomotopies
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponentConnected
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem protectedRegion_fundamentalGroup_map_eq_one
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {R C F : Set X}
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (f : C(Y, (R \ C : Set X))) (hf : ∀ y, (f y : X) ∈ F)
    (a : Y) (gamma : FundamentalGroup Y a) :
    FundamentalGroup.map f a gamma = 1 := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective gamma
  have hp := exists_frontier_loop_homotopy_in_protected_region
    hloops (f a) (p.map f.continuous) (fun t => hf (p t))
  rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  exact Path.Homotopic.Quotient.eq.mpr hp

theorem exists_original_frontier_component_sign_lift
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {R C F T : Set X} (HC : (A.edgeComponentComplex c).space ≃ₜ T)
    (hTF : T ⊆ F) (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    let J := A.edgeComponentComplex c
    let Z := plAtlasSignCore e hcover hcompat (R \ C)
    let f : C(J.space, (R \ C : Set X)) :=
      ⟨fun z => ⟨HC z, hFU (hTF (HC z).property)⟩,
        (continuous_subtype_val.comp HC.continuous).subtype_mk _⟩
    PathConnectedSpace J.space ∧ LocallyPathConnectedSpace J.space ∧
      PathConnectedSpace T ∧ LocallyPathConnectedSpace T ∧
      (∀ a gamma, FundamentalGroup.map f a gamma = 1) ∧
      ∃ (a0 : J.space) (L : C(J.space, Z.TotalSpace)),
        L a0 = (⟨f a0, (⟨1, one_ne_zero⟩ : PLOrientationSheet)⟩ : Z.TotalSpace) ∧
        (∀ z, Z.proj (L z) = f z) ∧
        ∃ sigma : C(T, Z.TotalSpace),
          (∀ y, sigma y = L (HC.symm y)) ∧
          ∀ y, Z.proj (sigma y) = ⟨y, hFU (hTF y.property)⟩ := by
  classical
  let J := A.edgeComponentComplex c
  let Z := plAtlasSignCore e hcover hcompat (R \ C)
  let f : C(J.space, (R \ C : Set X)) :=
    ⟨fun z => ⟨HC z, hFU (hTF (HC z).property)⟩,
      (continuous_subtype_val.comp HC.continuous).subtype_mk _⟩
  have hJ : J.faces.Finite := hA.subset (A.edgeComponentComplex_le c)
  let : PathConnectedSpace J.space :=
    isPathConnected_iff_pathConnectedSpace.mp (A.edgeComponentComplex_isPathConnected c)
  let : LocallyPathConnectedSpace J.space := J.locallyPathConnectedSpace_of_finite hJ
  have hpcT : PathConnectedSpace T := HC.surjective.pathConnectedSpace HC.continuous
  have hlpcT : LocallyPathConnectedSpace T :=
    HC.symm.isOpenEmbedding.locallyPathConnectedSpace
  have hkill (a : J.space) (gamma : FundamentalGroup J.space a) :
      FundamentalGroup.map f a gamma = 1 :=
    protectedRegion_fundamentalGroup_map_eq_one hloops f
      (fun z => hTF (HC z).property) a gamma
  let a0 : J.space := Classical.arbitrary _
  let e0 : Z.TotalSpace := ⟨f a0, (⟨1, one_ne_zero⟩ : PLOrientationSheet)⟩
  have hcov : IsCoveringMap Z.proj :=
    (plAtlasSignCore_covering e hcover hcompat (R \ C)).1
  have he : Z.proj e0 = f a0 := rfl
  have hrange : (FundamentalGroup.map f a0).range ≤
      (FundamentalGroup.mapOfEq (x := e0) ⟨Z.proj, hcov.continuous⟩ he).range := by
    rintro z ⟨gamma, rfl⟩
    rw [hkill]
    exact ⟨1, map_one _⟩
  obtain ⟨L, ⟨hLa0, hL⟩, _hunique⟩ :=
    hcov.existsUnique_continuousMap_lifts_of_range_le he hrange
  let sigma : C(T, Z.TotalSpace) := ⟨L ∘ HC.symm, L.continuous.comp HC.symm.continuous⟩
  refine ⟨inferInstance, inferInstance, hpcT, hlpcT, hkill,
    a0, L, hLa0, (fun z => congrFun hL z), sigma, (fun _ => rfl), ?_⟩
  intro y
  have h := congrFun hL (HC.symm y)
  have hbase : (Z.proj (L (HC.symm y)) : X) = (HC (HC.symm y) : X) :=
    congrArg (fun z : (R \ C : Set X) => (z : X)) h
  have hHC : (HC (HC.symm y) : X) = (y : X) :=
    congrArg (fun z : T => (z : X)) (HC.apply_symm_apply y)
  apply Subtype.ext
  exact hbase.trans hHC

end PoincareConjecture.M76
