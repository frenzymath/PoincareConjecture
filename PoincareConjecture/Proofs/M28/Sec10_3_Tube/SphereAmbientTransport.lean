import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SphereDisplacement
import Mathlib.Topology.UnitInterval











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)




theorem exists_local_sphere_ambient_transport
    {F : ℝ × UnitTwoSphere → E₃}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E₃) ∞ F)
    (t₀ : ℝ) (U : Set E₃)
    (hlocal : ∀ q : UnitTwoSphere, ∃ (V : Set E₃) (r : E₃ → UnitTwoSphere),
      IsOpen V ∧ F (t₀, q) ∈ V ∧ V ⊆ U ∧
      ContMDiffOn 𝓘(ℝ, E₃) (𝓡 2) ∞ r V ∧
      ∀ z : UnitTwoSphere, F (t₀, z) ∈ V → r (F (t₀, z)) = z) :
    ∃ (K : Set E₃) (J : Set ℝ), IsCompact K ∧ K ⊆ U ∧ IsOpen J ∧ t₀ ∈ J ∧
      ∀ s ∈ J, ∀ t ∈ J, ∃ e : E₃ ≃ₜ E₃,
        ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
        (∀ q : UnitTwoSphere, e (F (s, q)) = F (t, q)) ∧
        ∀ x : E₃, x ∉ K → e x = x := by
  obtain ⟨D, K, hD, hK, hKU, hsupport, hzero, hagree⟩ :=
    exists_compact_sphere_displacement hF t₀ U hlocal
  have hnear := eventually_exists_smooth_homeomorph_of_compact_displacement
    hD hK hsupport hzero
  obtain ⟨J, hJ, hJo, ht₀⟩ := mem_nhds_iff.mp hnear
  refine ⟨K, J, hK, hKU, hJo, ht₀, ?_⟩
  intro s hs t ht
  obtain ⟨es, hes, hess, hesi, hesfix⟩ := hJ hs
  obtain ⟨et, het, hets, heti, hetfix⟩ := hJ ht
  have hesq (q : UnitTwoSphere) : es (F (t₀, q)) = F (s, q) :=
    (congrFun hes (F (t₀, q))).trans (hagree s q)
  have hetq (q : UnitTwoSphere) : et (F (t₀, q)) = F (t, q) :=
    (congrFun het (F (t₀, q))).trans (hagree t q)
  refine ⟨es.symm.trans et, hets.comp hesi, hess.comp heti, ?_, ?_⟩
  · intro q
    change et (es.symm (F (s, q))) = F (t, q)
    rw [← hesq q, es.symm_apply_apply, hetq]
  · intro x hx
    have hsi : es.symm x = x := by
      calc
        es.symm x = es.symm (es x) := congrArg es.symm (hesfix x hx).symm
        _ = x := es.symm_apply_apply x
    change et (es.symm x) = x
    rw [hsi, hetfix x hx]





theorem exists_compact_sphere_ambient_transport
    {F : ℝ × UnitTwoSphere → E₃}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E₃) ∞ F)
    (U : Set E₃)
    (hlocal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q : UnitTwoSphere,
      ∃ (V : Set E₃) (r : E₃ → UnitTwoSphere),
        IsOpen V ∧ F (t, q) ∈ V ∧ V ⊆ U ∧
        ContMDiffOn 𝓘(ℝ, E₃) (𝓡 2) ∞ r V ∧
        ∀ z : UnitTwoSphere, F (t, z) ∈ V → r (F (t, z)) = z) :
    ∃ (K : Set E₃) (e : E₃ ≃ₜ E₃),
      IsCompact K ∧ K ⊆ U ∧ ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (∀ q : UnitTwoSphere, e (F (0, q)) = F (1, q)) ∧
      ∀ x : E₃, x ∉ K → e x = x := by
  classical
  let T : Type := ↥(Icc (0 : ℝ) 1)
  have hnear (t : T) :=
    exists_local_sphere_ambient_transport hF t.1 U (hlocal t.1 t.2)
  choose K J hK hKU hJo hJt htransport using hnear
  let cover : T → Set T := fun t => (Subtype.val : T → ℝ) ⁻¹' J t
  have hcovero (t : T) : IsOpen (cover t) :=
    (hJo t).preimage continuous_subtype_val
  have hcover : (univ : Set T) ⊆ ⋃ t : T, cover t := by
    intro t _
    exact mem_iUnion.mpr ⟨t, hJt t⟩
  obtain ⟨τ, hτ₀, hτmono, ⟨n, hn⟩, hpart⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcovero hcover
  choose c hc using hpart
  have hleft (i : ℕ) : (τ i : ℝ) ∈ J (c i) :=
    hc i (left_mem_Icc.mpr (hτmono (Nat.le_succ i)))
  have hright (i : ℕ) : (τ (i + 1) : ℝ) ∈ J (c i) :=
    hc i (right_mem_Icc.mpr (hτmono (Nat.le_succ i)))
  have hstep (i : ℕ) :=
    htransport (c i) (τ i) (hleft i) (τ (i + 1)) (hright i)
  choose e hes hei heq hefix using hstep
  let compose : ℕ → E₃ ≃ₜ E₃ :=
    Nat.rec (Homeomorph.refl E₃) (fun i previous => previous.trans (e i))
  have hsmooth (i : ℕ) :
      ContDiff ℝ ∞ (compose i) ∧ ContDiff ℝ ∞ (compose i).symm := by
    induction i with
    | zero => exact ⟨contDiff_id, contDiff_id⟩
    | succ i hi => exact ⟨(hes i).comp hi.1, hi.2.comp (hei i)⟩
  have hpath (i : ℕ) (q : UnitTwoSphere) :
      compose i (F (0, q)) = F ((τ i : ℝ), q) := by
    induction i with
    | zero =>
        change F (0, q) = F ((τ 0 : ℝ), q)
        rw [hτ₀]
        rfl
    | succ i hi =>
        change e i (compose i (F (0, q))) = F ((τ (i + 1) : ℝ), q)
        rw [hi, heq i q]
  have hfix (i : ℕ) (x : E₃) (hx : ∀ j < i, x ∉ K (c j)) : compose i x = x := by
    induction i with
    | zero => rfl
    | succ i hi =>
        change e i (compose i x) = x
        rw [hi (fun j hj => hx j (Nat.lt_succ_of_lt hj)), hefix i x (hx i (Nat.lt_succ_self i))]
  let Ksupport : Set E₃ := ⋃ i : Fin n, K (c i.1)
  have hcompact : IsCompact Ksupport := isCompact_iUnion (fun i : Fin n => hK (c i.1))
  have hsubset : Ksupport ⊆ U := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact hKU (c i.1) hxi
  refine ⟨Ksupport, compose n, hcompact, hsubset, (hsmooth n).1, (hsmooth n).2, ?_, ?_⟩
  · intro q
    simpa only [hn n le_rfl, Set.Icc.coe_one] using hpath n q
  · intro x hx
    apply hfix n x
    intro j hj hxj
    exact hx (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)

end PoincareConjecture.M28
