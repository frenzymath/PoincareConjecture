import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.IntegerMatrix
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import Mathlib.Data.Int.GCD



set_option autoImplicit false

open Set Topology Geometry

namespace PoincareConjecture.M76.LinearTorus


def primitiveMatrix (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a, -Int.gcdB a b; b, Int.gcdA a b]

theorem det_primitiveMatrix {a b : ℤ} (h : Int.gcd a b = 1) :
    (primitiveMatrix a b).det = 1 := by
  have hz := Int.gcd_eq_gcd_ab a b
  rw [h] at hz
  simpa [primitiveMatrix, Matrix.det_fin_two, sub_neg_eq_add, mul_comm] using hz.symm


def integerMatrixHomeomorph (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det = 1) : (AddCircle p × AddCircle p) ≃ₜ (AddCircle p × AddCircle p) where
  toFun := integerMatrixHom p A
  invFun := integerMatrixHom p A.adjugate
  left_inv x := by simpa [hA] using adjugate_integerMatrixHom p A x
  right_inv x := by simpa [hA] using integerMatrixHom_adjugate p A x
  continuous_toFun := continuous_integerMatrixHom p A
  continuous_invFun := continuous_integerMatrixHom p A.adjugate


def primitiveTorusBandMap (p : ℝ) (a b : ℤ) :
    C(AddCircle p × ℝ, AddCircle p × AddCircle p) :=
  (integerMatrixMap p (primitiveMatrix a b)).comp
    ⟨fun x => (x.1, (x.2 : AddCircle p)), by fun_prop⟩


def primitiveTorusBand (p : ℝ) (a b : ℤ) (r : ℝ) :
    C(AddCircle p × Icc (-r) r, AddCircle p × AddCircle p) :=
  (primitiveTorusBandMap p a b).comp
    ⟨fun x => (x.1, (x.2 : ℝ)), by fun_prop⟩

@[simp] theorem primitiveTorusBand_center (p : ℝ) (a b : ℤ) {r : ℝ}
    (hr : 0 ≤ r) (t : AddCircle p) :
    primitiveTorusBand p a b r (t, ⟨0, by constructor <;> linarith⟩) =
      (a • t, b • t) := by
  simp [primitiveTorusBand, primitiveTorusBandMap, primitiveMatrix,
    integerMatrixMap_apply]

theorem isEmbedding_primitiveTorusBand {p r : ℝ} (hp : 0 < p)
    {a b : ℤ} (hab : Int.gcd a b = 1) (hr : 2 * r < p) :
    IsEmbedding (primitiveTorusBand p a b r) := by
  let : Fact (0 < p) := ⟨hp⟩
  refine ((primitiveTorusBand p a b r).continuous.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  have heq : (x.1, ((x.2 : ℝ) : AddCircle p)) =
      (y.1, ((y.2 : ℝ) : AddCircle p)) :=
    (integerMatrixHomeomorph p (primitiveMatrix a b) (det_primitiveMatrix hab)).injective hxy
  apply Prod.ext
  · exact congrArg (fun z : AddCircle p × AddCircle p => z.1) heq
  apply Subtype.ext
  have hx : (x.2 : ℝ) ∈ Ico (-r) (-r + p) :=
    ⟨x.2.property.1, by linarith [x.2.property.2]⟩
  have hy : (y.2 : ℝ) ∈ Ico (-r) (-r + p) :=
    ⟨y.2.property.1, by linarith [y.2.property.2]⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp (congrArg Prod.snd heq)

theorem isOpenMap_primitiveTorusBandMap (p : ℝ) {a b : ℤ}
    (hab : Int.gcd a b = 1) : IsOpenMap (primitiveTorusBandMap p a b) := by
  exact (integerMatrixHomeomorph p (primitiveMatrix a b)
    (det_primitiveMatrix hab)).isOpenMap.comp
      (IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe)

theorem isOpen_primitiveTorusBand_inner (p : ℝ) {a b : ℤ}
    (hab : Int.gcd a b = 1) (r : ℝ) :
    IsOpen (primitiveTorusBand p a b r ''
      {x : AddCircle p × Icc (-r) r | -r < (x.2 : ℝ) ∧ (x.2 : ℝ) < r}) := by
  have heq : primitiveTorusBand p a b r ''
      {x : AddCircle p × Icc (-r) r | -r < (x.2 : ℝ) ∧ (x.2 : ℝ) < r} =
      primitiveTorusBandMap p a b '' (univ ×ˢ Ioo (-r) r) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x.1, x.2), ⟨mem_univ _, hx⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x.1, ⟨x.2, hx.2.1.le, hx.2.2.le⟩), hx.2, rfl⟩
  rw [heq]
  exact isOpenMap_primitiveTorusBandMap p hab _ (isOpen_univ.prod isOpen_Ioo)

theorem primitiveTorusBand_inner_mem_nhds (p : ℝ) {a b : ℤ}
    (hab : Int.gcd a b = 1) {r : ℝ} (hr : 0 < r) (t : AddCircle p) :
    primitiveTorusBand p a b r ''
      {x : AddCircle p × Icc (-r) r | -r < (x.2 : ℝ) ∧ (x.2 : ℝ) < r} ∈
      nhds (a • t, b • t) := by
  apply (isOpen_primitiveTorusBand_inner p hab r).mem_nhds
  exact ⟨(t, ⟨0, by constructor <;> linarith⟩),
    ⟨by dsimp; linarith, hr⟩, primitiveTorusBand_center p a b hr.le t⟩

theorem isCompact_range_primitiveTorusBand {p : ℝ} (hp : 0 < p)
    (a b : ℤ) (r : ℝ) : IsCompact (range (primitiveTorusBand p a b r)) := by
  let : Fact (0 < p) := ⟨hp⟩
  exact isCompact_range (primitiveTorusBand p a b r).continuous


def primitiveTorusBandLift (a b : ℤ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (((a : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) -
      ((Int.gcdB a b : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (((b : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      ((Int.gcdA a b : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem primitiveTorusBandMap_lift (p : ℝ) (a b : ℤ) (x : ℝ × ℝ) :
    primitiveTorusBandMap p a b ((x.1 : AddCircle p), x.2) =
      (((primitiveTorusBandLift a b x).1 : AddCircle p),
       ((primitiveTorusBandLift a b x).2 : AddCircle p)) := by
  simp [primitiveTorusBandMap, primitiveMatrix,
    primitiveTorusBandLift, sub_eq_add_neg]

theorem primitiveTorusBand_square_parameter (p : ℝ) (a b : ℤ) (r : ℝ)
    (x : Icc 0 p × Icc (-r) r) :
    primitiveTorusBand p a b r (((x.1 : ℝ) : AddCircle p), x.2) =
      (((primitiveTorusBandLift a b (x.1, x.2)).1 : AddCircle p),
       ((primitiveTorusBandLift a b (x.1, x.2)).2 : AddCircle p)) :=
  primitiveTorusBandMap_lift p a b (x.1, x.2)

theorem finitePiecewiseAffineOn_primitiveTorusBandLift (a b : ℤ)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (primitiveTorusBandLift a b) K.space := by
  exact (K.affineOnFaces_affine
    (primitiveTorusBandLift a b).toContinuousAffineMap).finitePiecewiseAffineOn hK

end PoincareConjecture.M76.LinearTorus
