import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSpherePairCharts
import PoincareConjecture.Proofs.M76.Brown.OrientedFlatteningCharts
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension
import Mathlib.Topology.Homeomorph.Lemmas











set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Metric Geometry SignType

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private noncomputable def normalLastCoordinates : V3 ≃ᴬ[ℝ] C3 :=
  let L : V3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x 1, x 2), x 0)
      invFun := fun z => ![z.2, z.1.1, z.1.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {S : Set X}

omit [T2Space X] in


theorem ChartwisePLSphere.lifting_connectedness (s : ChartwisePLSphere e S) :
    SimplyConnectedSpace S ∧ LocallyPathConnectedSpace S := by
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := s.parametrization.symm.trans
    (PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c)
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact ⟨H.toHomotopyEquiv.simplyConnectedSpace,
    H.isOpenEmbedding.locallyPathConnectedSpace⟩



theorem ChartwisePLSphere.exists_normal_flattening_atlas
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (e i).source) :
    ∃ A : BrownCollar.FlatteningAtlas (ℝ × ℝ) S S,
      A.indexAt = id ∧
      (∀ x : S, A.chart x x = 0) ∧
      ∀ i x, LocallyPiecewiseAffineOn ((e i).symm.trans (A.chart x))
        ((e i).symm.trans (A.chart x)).source := by
  classical
  choose B hxB hBx hB hBS using fun x : S =>
    s.exists_pair_chart hcompat hcover x.property
  let A : BrownCollar.FlatteningAtlas (ℝ × ℝ) S S :=
    { chart := fun x => (B x).transHomeomorph normalLastCoordinates.toHomeomorph
      pair := fun x y hy => hBS x y hy
      indexAt := id
      mem_source_at := hxB }
  refine ⟨A, rfl, ?_, ?_⟩
  · intro x
    change normalLastCoordinates (B x x) = 0
    rw [hBx]
    rfl
  · intro i x
    have h := (locallyPiecewiseAffineOn_affine
      normalLastCoordinates.toContinuousAffineMap isOpen_univ).comp (hB x i).1
    exact h.mono ((e i).symm.trans (A.chart x)).open_source
      (fun z hz => ⟨hz, mem_univ _⟩)

omit [T2Space X] in
private theorem exists_constant_normal_unit_domain
    (A : BrownCollar.FlatteningAtlas (ℝ × ℝ) S S)
    (a : S → S → SignTypeˣ)
    (ha : ∀ i, ContinuousOn (a i) (A.baseSet i)) (x : S) :
    ∃ O : Set X, IsOpen O ∧ (x : X) ∈ O ∧
      O ⊆ (A.chart (A.indexAt x)).source ∧
      ∀ b : S, (b : X) ∈ O → a (A.indexAt x) b = a (A.indexAt x) x := by
  let i := A.indexAt x
  let V := A.baseSet i ∩ a i ⁻¹' {a i x}
  have hV : IsOpen V := (ha i).isOpen_inter_preimage
    (A.isOpen_baseSet i) (isOpen_discrete _)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  have hxO : (x : X) ∈ O := by
    change x ∈ (Subtype.val : S → X) ⁻¹' O
    rw [hOV]
    exact ⟨A.mem_source_at x, rfl⟩
  refine ⟨O ∩ (A.chart i).source, hO.inter (A.chart i).open_source,
    ⟨hxO, A.mem_source_at x⟩, inter_subset_right, ?_⟩
  intro b hb
  have hbV : b ∈ V := by rw [← hOV]; exact hb.1
  exact hbV.2

omit [T2Space X] in
private theorem exists_oriented_charts_with_pl
    (A : BrownCollar.FlatteningAtlas (ℝ × ℝ) S S)
    (hA : ∀ i x, LocallyPiecewiseAffineOn ((e i).symm.trans (A.chart x))
      ((e i).symm.trans (A.chart x)).source)
    (a : S → S → SignTypeˣ)
    (ha : ∀ i, ContinuousOn (a i) (A.baseSet i))
    (hcompat : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      a j x = A.transitionUnit i j x * a i x) :
    ∃ E : S → OpenPartialHomeomorph X C3,
      (∀ x : S, (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0)) ∧
      (∀ i x, LocallyPiecewiseAffineOn ((e i).symm.trans (E x))
        ((e i).symm.trans (E x)).source) ∧
      ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          V ⊆ (E i).source ∩ (E j).source ∧
          EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V := by
  classical
  let I := A.indexAt
  let u : S → SignTypeˣ := fun x => a (I x) x
  choose O hO hxO hOA hconst using exists_constant_normal_unit_domain A a ha
  let E : S → OpenPartialHomeomorph X C3 := fun x =>
    BrownCollar.orientChart ((A.chart (I x)).restr (O x)) (u x)
  have hsource (i : S) : (E i).source = O i := by
    change ((A.chart (I i)).restr (O i)).source = O i
    rw [OpenPartialHomeomorph.restr_source' _ _ (hO i)]
    exact inter_eq_right.mpr (hOA i)
  have hnormal (i : S) (y : X) :
      (E i y).2 = BrownCollar.normalScalar (u i) * (A.chart (I i) y).2 := rfl
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hsource]
    exact hxO x
  · intro i y hy
    rw [hsource] at hy
    rw [hnormal, mul_eq_zero, or_iff_right (BrownCollar.normalScalar_ne_zero (u i))]
    exact A.pair (I i) y (hOA i hy)
  · intro j x
    let C := (e j).symm.trans ((A.chart (I x)).restr (O x))
    have hC : LocallyPiecewiseAffineOn C C.source :=
      (hA j (I x)).mono C.open_source (fun z hz => ⟨hz.1, hz.2.1⟩)
    let R : C3 →ᴬ[ℝ] C3 :=
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prodMap
        (BrownCollar.normalScalar (u x) • ContinuousLinearMap.id ℝ ℝ)).toContinuousAffineMap
    have hR := (locallyPiecewiseAffineOn_affine R isOpen_univ).comp hC
    exact hR.mono ((e j).symm.trans (E x)).open_source
      (fun z hz => ⟨hz, mem_univ _⟩)
  · intro i j x hx
    have hxi : (x : X) ∈ O i := by simpa only [hsource] using hx.1
    have hxj : (x : X) ∈ O j := by simpa only [hsource] using hx.2
    have hxA : x ∈ A.baseSet (I i) ∩ A.baseSet (I j) :=
      ⟨hOA i hxi, hOA j hxj⟩
    have hu := hcompat (I i) (I j) x hxA
    rw [hconst i x hxi, hconst j x hxj] at hu
    have huc : (u j : SignType) = A.transitionSign (I i) (I j) x * (u i : SignType) :=
      congrArg Units.val hu
    obtain ⟨_, T, hT, hxT, _, hsign⟩ := A.transitionSign_spec (I i) (I j) x hxA
    let V := (A.chart (I i)).source ∩ (A.chart (I i)) ⁻¹' T
    have hxVT : A.chart (I i) (x : X) ∈ T := by
      rw [← A.base_coordinate (I i) x hxA.1]
      exact hxT
    refine ⟨V ∩ ((E i).source ∩ (E j).source),
      ((A.chart (I i)).isOpen_inter_preimage hT).inter
        ((E i).open_source.inter (E j).open_source),
      ⟨⟨hxA.1, hxVT⟩, hx⟩, inter_subset_right, ?_⟩
    intro y hy
    have hsigny := hsign (A.chart (I i) y) hy.1.2
    change sign (A.chart (I j) ((A.chart (I i)).symm (A.chart (I i) y))).2 =
      A.transitionSign (I i) (I j) x * sign (A.chart (I i) y).2 at hsigny
    rw [(A.chart (I i)).left_inv hy.1.1] at hsigny
    change sign (E i y).2 = sign (E j y).2
    rw [hnormal, hnormal, BrownCollar.normalScalar_sign,
      BrownCollar.normalScalar_sign, hsigny, huc]
    have hsq : A.transitionSign (I i) (I j) x * A.transitionSign (I i) (I j) x = 1 :=
      mul_inv_cancel₀ (A.transitionSign_ne_zero (I i) (I j) x)
    calc
      _ = (A.transitionSign (I i) (I j) x * A.transitionSign (I i) (I j) x) *
          ((u i : SignType) * sign (A.chart (I i) y).2) := by rw [hsq, one_mul]
      _ = _ := by ac_rfl




theorem ChartwisePLSphere.exists_coherently_oriented_pair_charts
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (e i).source) :
    ∃ B : S → OpenPartialHomeomorph X V3,
      (∀ x : S, (x : X) ∈ (B x).source) ∧
      (∀ i y, y ∈ (B i).source → (y ∈ S ↔ (B i y) 0 = 0)) ∧
      (∀ i x, (e i).symm.trans (B x) ∈ piecewiseAffineGroupoid V3) ∧
      ∀ i j (x : S), (x : X) ∈ (B i).source ∩ (B j).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          V ⊆ (B i).source ∩ (B j).source ∧
          EqOn (fun y => sign ((B i y) 0)) (fun y => sign ((B j y) 0)) V := by
  let : SimplyConnectedSpace S := s.lifting_connectedness.1
  let : LocallyPathConnectedSpace S := s.lifting_connectedness.2
  obtain ⟨x0, hx0⟩ :=
    (show (sphere (0 : V3) 1).Nonempty from NormedSpace.sphere_nonempty.mpr zero_le_one)
  let : Nonempty S := ⟨s.parametrization ⟨x0, hx0⟩⟩
  obtain ⟨A, _, _, hA⟩ := s.exists_normal_flattening_atlas hcompat hcover
  obtain ⟨a, ha, hac⟩ := A.exists_coherent_normal_units
  obtain ⟨E, hxE, hES, hE, hagree⟩ := exists_oriented_charts_with_pl A hA a ha hac
  let B := fun x => (E x).transHomeomorph normalLastCoordinates.symm.toHomeomorph
  refine ⟨B, hxE, hES, ?_, hagree⟩
  intro i x
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have h := (locallyPiecewiseAffineOn_affine
    normalLastCoordinates.symm.toContinuousAffineMap isOpen_univ).comp (hE i x)
  exact h.mono ((e i).symm.trans (B x)).open_source
    (fun z hz => ⟨hz, mem_univ _⟩)

end PoincareConjecture.M76
