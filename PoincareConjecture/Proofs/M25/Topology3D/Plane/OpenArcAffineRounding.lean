import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcRounding

set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}

theorem IsSimplePolygonalArc.map_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (A : E →ᵃ[ℝ] F) (hA : Injective A) :
    IsSimplePolygonalArc (⟨fun k => A (p k)⟩ : Polygon F (n + 2)) := by
  let q : Polygon F (n + 2) := ⟨fun k => A (p k)⟩
  refine ⟨hA.comp hp.vertices_injective, ?_⟩
  intro i j hij x hx
  have hxi : x ∈ A '' segment ℝ (p i.castSucc) (p i.succ) := by
    rw [image_segment]
    simpa only [polygon_arcEdge_eq_segment, q] using hx.1
  have hxj : x ∈ A '' segment ℝ (p j.castSucc) (p j.succ) := by
    rw [image_segment]
    simpa only [polygon_arcEdge_eq_segment, q] using hx.2
  obtain ⟨y, hy, hyx⟩ := hxi
  obtain ⟨z, hz, hzx⟩ := hxj
  have hyz : y = z := hA (hyx.trans hzx.symm)
  subst z
  have hends := hp.edges_inter i j hij
    (show y ∈ p.edgeSet ℝ i.castSucc ∩ p.edgeSet ℝ j.castSucc by
      simpa only [polygon_arcEdge_eq_segment, mem_inter_iff] using And.intro hy hz)
  constructor
  · rcases hends.1 with h | h
    · exact Or.inl (hyx.symm.trans (congrArg A h))
    · exact Or.inr (hyx.symm.trans (congrArg A h))
  · rcases hends.2 with h | h
    · exact Or.inl (hyx.symm.trans (congrArg A h))
    · exact Or.inr (hyx.symm.trans (congrArg A h))

theorem affineMap_roundedVertexPath {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ᵃ[ℝ] F) (ρ : ℝ → ℝ) (P : ℤ → E) (u : ℝ) :
    A (roundedVertexPath ρ P u) =
      roundedVertexPath ρ (fun j => A (P j)) u := by
  have hformula (x y z : E) (a d : ℝ) :
      A (x + a • (x - y) + d • (z - x)) =
        A x + a • (A x - A y) + d • (A z - A x) := by
    rw [congrFun A.decomp (x + a • (x - y) + d • (z - x)),
      congrFun A.decomp x, congrFun A.decomp y, congrFun A.decomp z]
    simp only [Pi.add_apply, map_add, map_smul, map_sub]
    module
  exact hformula _ _ _ _ _

noncomputable def normalizeOpenArc (a h : ℝ) (p : Polygon (ℝ × ℝ) (n + 2)) :
    Polygon (ℝ × ℝ) (n + 2) :=
  ⟨fun k => h⁻¹ • (p k - (a, 0))⟩

noncomputable def affineRoundedOpenArcParameter (ρ : ℝ → ℝ) (a h : ℝ)
    (p : Polygon (ℝ × ℝ) (n + 2)) (u : ℝ) : ℝ × ℝ :=
  (a, 0) + h • roundedOpenArcParameter ρ (normalizeOpenArc a h p) ((u - a) / h)

private noncomputable def normalizeOpenArcMap (a h : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun := fun x => h⁻¹ • (x - (a, 0))
  linear := h⁻¹ • LinearMap.id
  map_vadd' := by intro p v; dsimp; module

theorem normalizeOpenArc_good {a h : ℝ} (hh : 0 < h)
    (p : Polygon (ℝ × ℝ) (n + 2))
    (hp : IsSimplePolygonalArc p) (h0 : p 0 = (a, 0))
    (hN : p (Fin.last (n + 1)) = (a + h * (n + 1 : ℕ), 0))
    (hstrip : ∀ k, k ≠ 0 → k ≠ Fin.last (n + 1) →
      a < (p k).1 ∧ (p k).1 < a + h * (n + 1 : ℕ)) :
    IsSimplePolygonalArc (normalizeOpenArc a h p) ∧
      normalizeOpenArc a h p 0 = (0, 0) ∧
      normalizeOpenArc a h p (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0) ∧
      ∀ k, k ≠ 0 → k ≠ Fin.last (n + 1) →
        0 < (normalizeOpenArc a h p k).1 ∧
          (normalizeOpenArc a h p k).1 < (n + 1 : ℕ) := by
  have hA : Injective (normalizeOpenArcMap a h) := by
    intro x y hxy
    exact sub_left_injective
      (smul_right_injective (ℝ × ℝ) (inv_ne_zero hh.ne') hxy)
  refine ⟨hp.map_affine (normalizeOpenArcMap a h) hA, ?_, ?_, ?_⟩
  · change h⁻¹ • (p 0 - (a, 0)) = (0, 0)
    rw [h0, sub_self, smul_zero]
    rfl
  · change h⁻¹ • (p (Fin.last (n + 1)) - (a, 0)) = _
    rw [hN]
    ext <;> dsimp <;> field_simp <;> ring
  · intro k hk0 hkN
    obtain ⟨hlo, hhi⟩ := hstrip k hk0 hkN
    change 0 < h⁻¹ * ((p k).1 - a) ∧ h⁻¹ * ((p k).1 - a) < (n + 1 : ℕ)
    refine ⟨mul_pos (inv_pos.mpr hh) (sub_pos.mpr hlo), ?_⟩
    calc
      h⁻¹ * ((p k).1 - a) < h⁻¹ * ((a + h * (n + 1 : ℕ)) - a) :=
        mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hh)
      _ = (n + 1 : ℕ) := by field_simp; ring

theorem affineRoundedOpenArcParameter_eq_samples {a h R : ℝ} (hh : 0 < h)
    (C : ℝ → ℝ × ℝ) (p : Polygon (ℝ × ℝ) (n + 2))
    (ha : a ≤ -R) (hb : R ≤ a + h * (n + 1 : ℕ))
    (htail : ∀ x, R ≤ |x| → C x = (x, 0))
    (hsample : ∀ k, p k = C (a + h * (k.val : ℝ)))
    (ρ : ℝ → ℝ) (u : ℝ) :
    affineRoundedOpenArcParameter ρ a h p u =
      roundedVertexPath ρ (fun i : ℤ => C (a + h * i)) ((u - a) / h) := by
  let A : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
    { toFun := fun x => (a, 0) + h • x
      linear := h • LinearMap.id
      map_vadd' := by intro x v; dsimp; module }
  have hfinite (k : Fin (n + 2)) :
      A (openArcExtendedVertex (normalizeOpenArc a h p) (k.val : ℤ)) =
        C (a + h * (k.val : ℝ)) := by
    rw [openArcExtendedVertex_nat]
    change (a, 0) + h • (h⁻¹ • (p k - (a, 0))) = _
    rw [smul_smul, mul_inv_cancel₀ hh.ne', one_smul, add_sub_cancel, hsample]
  have hvertex (i : ℤ) :
      A (openArcExtendedVertex (normalizeOpenArc a h p) i) = C (a + h * i) := by
    by_cases hi : 0 ≤ i ∧ i ≤ (n + 1 : ℕ)
    · let k : Fin (n + 2) := ⟨i.toNat, (Int.toNat_lt hi.1).mpr (by omega)⟩
      have hk : (k.val : ℤ) = i := Int.toNat_of_nonneg hi.1
      rw [← hk]
      simpa only [Int.cast_natCast] using hfinite k
    · have hR : R ≤ |a + h * (i : ℝ)| := by
        by_cases hi0 : i < 0
        · have hi0' : (i : ℝ) < 0 := by exact_mod_cast hi0
          exact (show R ≤ -(a + h * (i : ℝ)) by nlinarith).trans (neg_le_abs _)
        · have hiN : (n + 1 : ℕ) < i := by omega
          have hiN' : ((n + 1 : ℕ) : ℝ) < i := by exact_mod_cast hiN
          exact (show R ≤ a + h * (i : ℝ) by nlinarith).trans (le_abs_self _)
      rw [htail _ hR]
      change (a, 0) + h • openArcExtendedVertex (normalizeOpenArc a h p) i = _
      rw [show openArcExtendedVertex (normalizeOpenArc a h p) i = ((i : ℝ), 0) from if_neg hi]
      ext <;> simp
  change A (roundedVertexPath ρ (openArcExtendedVertex (normalizeOpenArc a h p))
    ((u - a) / h)) = _
  rw [affineMap_roundedVertexPath]
  exact congrArg (fun P : ℤ → ℝ × ℝ => roundedVertexPath ρ P ((u - a) / h)) (funext hvertex)

end PoincareConjecture.M25.Topology3D
