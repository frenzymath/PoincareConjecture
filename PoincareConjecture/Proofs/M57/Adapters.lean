import PoincareConjecture.Definitions.M57Transport












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m57SurgeryHomotopyMap_one
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {n : ℕ} [Nonempty (Fin n)]
    (f : ContinuousMap X Y) (h : f x = y) :
    surgeryHomotopyMap (n := n) f h
        (1 : HomotopyGroup.Pi n X x) = 1 := by
  rw [HomotopyGroup.one_def]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  change f x = y
  exact h

theorem m57SurgeryHomotopyMap_comp
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {x : X} {y : Y} {z : Z} {n : ℕ}
    (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    (h : f x = y) (k : g y = z) (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap (n := n) g k
        (surgeryHomotopyMap (n := n) f h a) =
      surgeryHomotopyMap (n := n) (g.comp f) ((congrArg g h).trans k) a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro q
    rfl

theorem m57SurgeryHomotopyMap_id
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap (n := n) (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro q
    rfl

theorem m57SurgeryHomotopyMap_eq_id
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (f : ContinuousMap X X) (hfx : f x = x)
    (hfun : f = ContinuousMap.id X) (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap (n := n) f hfx a = a := by
  subst f
  exact m57SurgeryHomotopyMap_id a

theorem m57SurgeryHomotopyMap_bijective_of_inverse
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap X Y) (g : ContinuousMap Y X)
    (h : f x = y) (hgf : g y = x)
    (hgf_map : g.comp f = ContinuousMap.id X)
    (hfg_map : f.comp g = ContinuousMap.id Y) :
    Function.Bijective (surgeryHomotopyMap (n := 3) f h) := by
  constructor
  · intro a b hab
    have hcomp_eq := congrArg
      (surgeryHomotopyMap (n := 3) g hgf) hab
    have hcomp_a := m57SurgeryHomotopyMap_comp f g h hgf a
    have hcomp_b := m57SurgeryHomotopyMap_comp f g h hgf b
    have hcomp_eq' :
        surgeryHomotopyMap (n := 3) (g.comp f)
            ((congrArg g h).trans hgf) a =
          surgeryHomotopyMap (n := 3) (g.comp f)
            ((congrArg g h).trans hgf) b := by
      exact hcomp_a.symm.trans (hcomp_eq.trans hcomp_b)
    calc
      a = surgeryHomotopyMap (n := 3) (g.comp f)
          ((congrArg g h).trans hgf) a :=
        (m57SurgeryHomotopyMap_eq_id (g.comp f)
          ((congrArg g h).trans hgf) hgf_map a).symm
      _ = surgeryHomotopyMap (n := 3) (g.comp f)
          ((congrArg g h).trans hgf) b := hcomp_eq'
      _ = b := m57SurgeryHomotopyMap_eq_id (g.comp f)
        ((congrArg g h).trans hgf) hgf_map b
  · intro b
    refine ⟨surgeryHomotopyMap (n := 3) g hgf b, ?_⟩
    have hcomp_eq := m57SurgeryHomotopyMap_comp g f hgf h b
    have hcomp_eq_comp :
        surgeryHomotopyMap (n := 3) (f.comp g)
            ((congrArg f hgf).trans h) b = b := by
      exact m57SurgeryHomotopyMap_eq_id (f.comp g)
        ((congrArg f hgf).trans h) hfg_map b
    exact hcomp_eq.trans hcomp_eq_comp

theorem m57SurgeryHomotopyMap_bijective_of_diffeomorph
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B]
    (f : Diffeomorph (𝓡 3) (𝓡 3) A B ∞) (x : A) :
    Function.Bijective
      (surgeryHomotopyMap (n := 3)
        (repairedDiffeomorphContinuousMap f) (rfl : f x = f x)) := by
  let fc : ContinuousMap A B := repairedDiffeomorphContinuousMap f
  let gc : ContinuousMap B A := repairedDiffeomorphContinuousMap f.symm
  have hgf : gc (fc x) = x := by
    exact f.left_inv x
  have hgf_map : gc.comp fc = ContinuousMap.id A := by
    ext z
    exact f.left_inv z
  have hfg_map : fc.comp gc = ContinuousMap.id B := by
    ext z
    exact f.right_inv z
  exact m57SurgeryHomotopyMap_bijective_of_inverse
    fc gc (rfl : fc x = fc x) hgf hgf_map hfg_map

theorem m57NonzeroTransport_of_bijective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap X Y) (h : f x = y)
    (hf : Function.Bijective
      (surgeryHomotopyMap (n := 3) f h))
    {a : HomotopyGroup.Pi 3 X x} (ha : a ≠ 1) :
    surgeryHomotopyMap (n := 3) f h a ≠ 1 := by
  intro h1
  apply ha
  apply hf.1
  rw [m57SurgeryHomotopyMap_one f h]
  exact h1

theorem m57RegularNonzeroTransport_of_diffeomorph
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B]
    (f : Diffeomorph (𝓡 3) (𝓡 3) A B ∞) (x : A)
    (T : M59HigherBasepointTransport B 3)
    {y : B} (p : Path (repairedDiffeomorphContinuousMap f x) y)
    {alpha : HomotopyGroup.Pi 3 A x} (ha : alpha ≠ 1) :
    M59HigherBasepointTransport.map T p
      (surgeryHomotopyMap (n := 3)
        (repairedDiffeomorphContinuousMap f) (rfl : f x = f x) alpha) ≠ 1 := by
  have hbij := m57SurgeryHomotopyMap_bijective_of_diffeomorph f x
  have hfa := m57NonzeroTransport_of_bijective
    (repairedDiffeomorphContinuousMap f) (rfl : f x = f x) hbij ha
  intro hzero
  have hinv := congrArg
    (M59HigherBasepointTransport.map T p.symm) hzero
  have hback :
      M59HigherBasepointTransport.map T p.symm
        (M59HigherBasepointTransport.map T p
          (surgeryHomotopyMap (n := 3)
            (repairedDiffeomorphContinuousMap f) (rfl : f x = f x) alpha)) =
        surgeryHomotopyMap (n := 3)
          (repairedDiffeomorphContinuousMap f) (rfl : f x = f x) alpha :=
    T.map_left_inverse p _
  have hone :
      M59HigherBasepointTransport.map T p.symm (1 : HomotopyGroup.Pi 3 B y) = 1 :=
    T.map_one p.symm
  apply hfa
  rw [hback] at hinv
  rw [hone] at hinv
  exact hinv









theorem m57AncestryTransport_of_input
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService) :
    Nonempty (RepairedAncestryTransportData D W P K C H B) := by
  classical
  let output := fun (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier) =>
    fun hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants =>
      fun hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants =>
        (Classical.choice (C.transport S.1 hS
          (H.event_input S hS hpost) hdelta hh)).val
  refine ⟨{
    event_output := output,
    event_output_eq_provider := ?_,
    event_nonzero_transport := ?_,
    regular_nonzero_transport := ?_ }⟩
  · intro S hS hpost hdelta hh
    rfl
  · intro S hS hpost hdelta hh alpha ha
    exact m57NonzeroTransport_of_bijective
      (output S hS hpost hdelta hh).comparison.map
      (output S hS hpost hdelta hh).comparison.based
      (output S hS hpost hdelta hh).pi_three_bijective ha
  · intro a b hab hdisjoint alpha ha y p
    exact m57RegularNonzeroTransport_of_diffeomorph
      (P.regular_transport a b hab hdisjoint)
      (P.component a).basepoint (B.transport 3) p ha

set_option linter.style.haveILetI false in
theorem m57RegularBasepointBridge_of_connected_target
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B]
    [ConnectedSpace B]
    (f : Diffeomorph (𝓡 3) (𝓡 3) A B ∞)
    (x : A) (y : B) :
    Nonempty (Path (repairedDiffeomorphContinuousMap f x) y) := by
  letI : LocallyPathConnectedSpace B :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin 3)) B
  letI : PathConnectedSpace B :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact ⟨PathConnectedSpace.somePath
    (repairedDiffeomorphContinuousMap f x) y⟩

end PoincareConjecture
