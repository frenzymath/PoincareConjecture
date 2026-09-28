import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierComponentLift
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasLiftLabels











set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem exists_original_frontier_component_sign_labels
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
    let V : ι → Set J.space := fun i => {z | (f z : X) ∈ (e i).source}
    PathConnectedSpace J.space ∧ LocallyPathConnectedSpace J.space ∧
      PathConnectedSpace T ∧ LocallyPathConnectedSpace T ∧
      (∀ a gamma, FundamentalGroup.map f a gamma = 1) ∧
      ∃ (a0 : J.space) (L : C(J.space, Z.TotalSpace)),
        L a0 = (⟨f a0, (⟨1, one_ne_zero⟩ : PLOrientationSheet)⟩ : Z.TotalSpace) ∧
        (∀ z, Z.proj (L z) = f z) ∧
        (∃ sigma : C(T, Z.TotalSpace),
          (∀ y, sigma y = L (HC.symm y)) ∧
          ∀ y, Z.proj (sigma y) = ⟨y, hFU (hTF y.property)⟩) ∧
        (∀ i, IsOpen (V i)) ∧
        ∃ label : ∀ i, LocallyConstant (V i) PLOrientationSheet,
          (∀ i y, label i y = ((Z.localTriv i) (L y)).2) ∧
          ∀ i j y (hi : y ∈ V i) (hj : y ∈ V j),
            (label j ⟨y, hj⟩).val =
              plAtlasTransitionSign e hcompat i j ⟨f y, hi, hj⟩ *
                (label i ⟨y, hi⟩).val := by
  let J := A.edgeComponentComplex c
  let f : C(J.space, (R \ C : Set X)) :=
    ⟨fun z => ⟨HC z, hFU (hTF (HC z).property)⟩,
      (continuous_subtype_val.comp HC.continuous).subtype_mk _⟩
  obtain ⟨hpc, hlpc, hpcT, hlpcT, hkill, a0, L, hLa0, hL,
    sigma, hsigmaval, hsigma⟩ :=
    exists_original_frontier_component_sign_lift e hcover hcompat A hA c HC hTF hFU hloops
  have hlabels := exists_plAtlasSign_lift_labels e hcover hcompat (R \ C) f L hL
  exact ⟨hpc, hlpc, hpcT, hlpcT, hkill, a0, L, hLa0, hL,
    ⟨sigma, hsigmaval, hsigma⟩, hlabels⟩

end PoincareConjecture.M76
