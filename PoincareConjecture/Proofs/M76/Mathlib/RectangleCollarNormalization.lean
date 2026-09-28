import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectangleSides











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePL.exists_bottom_normalized_rectangle_chart
    {α β : ℝ} (hαβ : α < β) {T : Set E}
    {G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T}
    (hG : G.IsFinitePL) (A : E → ℝ)
    (hheight : ∀ p, A (G p) = (p : ℝ × ℝ).2) :
    ∃ C : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ T,
      C.IsFinitePL ∧ (∀ p, A (C p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ T ∩ {x | A x = α}),
        (C ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ (p : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)))
        (u : Icc (0 : ℝ) 1),
        (G ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = (p : E × ℝ).1 →
        (C p : E) = G ⟨(u, (p : E × ℝ).2), ⟨u.property, p.property.2⟩⟩ := by
  have hcopy := hG
  obtain ⟨f, hf, hGf⟩ := hcopy
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  let i : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ α)
  have hi : FinitePiecewiseAffineOn i (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine i⟩
  have hFi : FinitePiecewiseAffineOn (f ∘ i) (Icc (0 : ℝ) 1) :=
    hf.comp hi (fun _ hx => ⟨hx, le_rfl, hαβ.le⟩)
  have hval (u : Icc (0 : ℝ) 1) : (f ∘ i) u =
      (G ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) := by
    exact (hGf ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩).symm
  have hinj : InjOn (f ∘ i) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have heq : G ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ =
        G ⟨(y, α), ⟨hy, ⟨le_rfl, hαβ.le⟩⟩⟩ :=
      Subtype.ext ((hval ⟨x, hx⟩).symm.trans (hxy.trans (hval ⟨y, hy⟩)))
    exact congrArg Prod.fst (congrArg Subtype.val (G.injective heq))
  have himage : (f ∘ i) '' Icc (0 : ℝ) 1 = T ∩ {x | A x = α} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hval ⟨u, hu⟩]
      exact ⟨(G ⟨(u, α), ⟨hu, ⟨le_rfl, hαβ.le⟩⟩⟩).property, hheight _⟩
    · intro hx
      let p := G.symm ⟨x, hx.1⟩
      have hp : (G p : E) = x := congrArg Subtype.val (G.apply_symm_apply _)
      have hpa : (p : ℝ × ℝ).2 = α :=
        (hheight p).symm.trans ((congrArg A hp).trans hx.2)
      have heq : (⟨((p : ℝ × ℝ).1, α),
          ⟨p.property.1, ⟨le_rfl, hαβ.le⟩⟩⟩ :
          (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ))) = p :=
        Subtype.ext (Prod.ext rfl hpa.symm)
      refine ⟨(p : ℝ × ℝ).1, p.property.1, ?_⟩
      rw [hval ⟨(p : ℝ × ℝ).1, p.property.1⟩, heq]
      exact hp
  have hBexists := hFi.exists_homeomorph_image hinj
  rw [himage] at hBexists
  obtain ⟨b, hb, hbval₀⟩ := hBexists
  have hbval (u : Icc (0 : ℝ) 1) : (b u : E) =
      G ⟨(u, α), ⟨u.property, ⟨le_rfl, hαβ.le⟩⟩⟩ := (hbval₀ u).trans (hval u)
  have hheightI := isFinitePLBallPair_Icc hαβ
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hheightI
  have hid : (Homeomorph.refl (Icc α β)).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ => rfl⟩
  let P := (Homeomorph.Set.prod (T ∩ {x | A x = α}) (Icc α β)).trans
    ((b.symm.prodCongr (Homeomorph.refl (Icc α β))).trans
      (Homeomorph.Set.prod (Icc (0 : ℝ) 1) (Icc α β)).symm)
  let C := P.trans G
  refine ⟨C, (hb.symm.prod hid).trans hG, fun p => hheight (P p), ?_, ?_⟩
  · intro x hx
    exact (hbval (b.symm ⟨x, hx⟩)).symm.trans
      (congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩))
  · intro p u hu
    have hbu : b u = ⟨(p : E × ℝ).1, p.property.1⟩ :=
      Subtype.ext ((hbval u).trans hu)
    have hbinv : b.symm ⟨(p : E × ℝ).1, p.property.1⟩ = u := by
      rw [← hbu, b.symm_apply_apply]
    change (G ⟨((b.symm ⟨(p : E × ℝ).1, p.property.1⟩ : ℝ), (p : E × ℝ).2), _⟩ : E) =
      G ⟨(u, (p : E × ℝ).2), _⟩
    exact congrArg (fun z : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) => (G z : E))
      (Subtype.ext (Prod.ext (congrArg Subtype.val hbinv) rfl))

end Homeomorph
