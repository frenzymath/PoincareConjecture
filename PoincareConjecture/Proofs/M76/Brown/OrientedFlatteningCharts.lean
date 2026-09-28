import PoincareConjecture.Proofs.M76.Brown.NormalBundleSection
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.NormNum










set_option autoImplicit false

open Set SignType

namespace BrownCollar

def normalScalar (s : SignTypeˣ) : ℝ := SignType.cast (s : SignType)

private theorem sign_real_cast (s : SignType) : sign (SignType.cast s : ℝ) = s := by
  cases s <;> norm_num [SignType.cast, sign_apply]

theorem normalScalar_ne_zero (s : SignTypeˣ) : normalScalar s ≠ 0 := by
  intro h
  have hsign := congrArg (fun r : ℝ => sign r) h
  rw [normalScalar, sign_real_cast, sign_zero] at hsign
  exact s.ne_zero hsign

theorem normalScalar_sign (s : SignTypeˣ) (t : ℝ) :
    sign (normalScalar s * t) = (s : SignType) * sign t := by
  rw [sign_mul, normalScalar, sign_real_cast]

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]



noncomputable def orientChart (e : OpenPartialHomeomorph X (P × ℝ)) (s : SignTypeˣ) :
    OpenPartialHomeomorph X (P × ℝ) :=
  e.transHomeomorph ((Homeomorph.refl P).prodCongr
    (Homeomorph.mulLeft₀ (normalScalar s) (normalScalar_ne_zero s)))

private theorem exists_constant_unit_domain {S : Set X}
    (e : OpenPartialHomeomorph X (P × ℝ)) (a : S → SignTypeˣ)
    (ha : ContinuousOn a ((Subtype.val : S → X) ⁻¹' e.source))
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ O : Set X, IsOpen O ∧ (x : X) ∈ O ∧ O ⊆ e.source ∧
      ∀ b : S, (b : X) ∈ O → a b = a x := by
  let W := (Subtype.val : S → X) ⁻¹' e.source
  let V := W ∩ a ⁻¹' {a x}
  have hV : IsOpen V := ha.isOpen_inter_preimage
    (e.open_source.preimage continuous_subtype_val) (isOpen_discrete _)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  have hxV : x ∈ V := ⟨hx, rfl⟩
  have hxO : (x : X) ∈ O := by
    change x ∈ (Subtype.val : S → X) ⁻¹' O
    rw [hOV]
    exact hxV
  refine ⟨O ∩ e.source, hO.inter e.open_source, ⟨hxO, hx⟩,
    inter_subset_right, ?_⟩
  intro b hb
  have hbV : b ∈ V := by
    rw [← hOV]
    exact hb.1
  exact hbV.2

end BrownCollar

namespace BrownCollar.FlatteningAtlas

variable {X P ι : Type*} [TopologicalSpace X] [NormedAddCommGroup P]
  [NormedSpace ℝ P] {S : Set X} (A : FlatteningAtlas P S ι)




theorem exists_oriented_charts (a : ι → S → SignTypeˣ)
    (ha : ∀ i, ContinuousOn (a i) (A.baseSet i))
    (hcompat : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      a j x = A.transitionUnit i j x * a i x) :
    ∃ E : S → OpenPartialHomeomorph X (P × ℝ),
      (∀ x : S, (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0)) ∧
      ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V := by
  classical
  let I := A.indexAt
  let u : S → SignTypeˣ := fun x => a (I x) x
  have hchoose (x : S) : ∃ O : Set X,
      IsOpen O ∧ (x : X) ∈ O ∧ O ⊆ (A.chart (I x)).source ∧
      ∀ b : S, (b : X) ∈ O → a (I x) b = u x :=
    exists_constant_unit_domain (A.chart (I x)) (a (I x)) (ha (I x)) x
      (A.mem_source_at x)
  choose O hO hxO hOA hconst using hchoose
  let E : S → OpenPartialHomeomorph X (P × ℝ) := fun x =>
    orientChart ((A.chart (I x)).restr (O x)) (u x)
  have hsource (i : S) : (E i).source = O i := by
    change ((A.chart (I i)).restr (O i)).source = O i
    rw [OpenPartialHomeomorph.restr_source' _ _ (hO i)]
    exact inter_eq_right.mpr (hOA i)
  have hnormal (i : S) (y : X) :
      (E i y).2 = normalScalar (u i) * (A.chart (I i) y).2 := rfl
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x
    rw [hsource]
    exact hxO x
  · intro i y hy
    rw [hsource] at hy
    rw [hnormal, mul_eq_zero, or_iff_right (normalScalar_ne_zero (u i))]
    exact A.pair (I i) y (hOA i hy)
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
    refine ⟨V, (A.chart (I i)).isOpen_inter_preimage hT, ⟨hxA.1, hxVT⟩, ?_⟩
    intro y hy
    have hyA : y ∈ (A.chart (I i)).source := hy.1
    have hsigny := hsign (A.chart (I i) y) hy.2
    change sign (A.chart (I j) ((A.chart (I i)).symm (A.chart (I i) y))).2 =
      A.transitionSign (I i) (I j) x * sign (A.chart (I i) y).2 at hsigny
    rw [(A.chart (I i)).left_inv hyA] at hsigny
    change sign (E i y).2 = sign (E j y).2
    rw [hnormal, hnormal, normalScalar_sign, normalScalar_sign, hsigny, huc]
    have hsq : A.transitionSign (I i) (I j) x * A.transitionSign (I i) (I j) x = 1 :=
      mul_inv_cancel₀ (A.transitionSign_ne_zero (I i) (I j) x)
    calc
      _ = (A.transitionSign (I i) (I j) x * A.transitionSign (I i) (I j) x) *
          ((u i : SignType) * sign (A.chart (I i) y).2) := by rw [hsq, one_mul]
      _ = _ := by ac_rfl

end BrownCollar.FlatteningAtlas
