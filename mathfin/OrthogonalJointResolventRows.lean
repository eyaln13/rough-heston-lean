import TiltingItoPairing
import OrthogonalClusterMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped MeasureTheory NNReal ENNReal InnerProductSpace Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝒢 : Filtration ℝ≥0 m} {X Y : ℝ≥0 → Ω → ℝ}

private theorem orthogonal_weighted_increment_zero
    (hX : Martingale X 𝒢 μ) (hX₂ : ∀ t, MemLp (X t) 2 μ)
    {s t : ℝ≥0} (hst : s≤t) {w : Ω → ℝ}
    (hw : StronglyMeasurable[𝒢 s] w) (hw₂ : MemLp w 2 μ) :
    (∫ ω,w ω*(X t ω-X s ω) ∂μ)=0 := by
  let d := X t-X s
  have hd₂ : MemLp d 2 μ := (hX₂ t).sub (hX₂ s)
  have hi : Integrable (w*d) μ := hw₂.integrable_mul hd₂
  have he := (condExp_mul_of_stronglyMeasurable_left hw hi (hd₂.integrable (by norm_num))).trans
    (EventuallyEq.rfl.mul (conditional_mean_martingale_increment hX hst))
  calc
    _ = ∫ ω,μ[w*d | 𝒢 s] ω ∂μ := (integral_condExp (𝒢.le s)).symm
    _ = _ := by
      apply (integral_congr_ae he).trans
      simp

private theorem orthogonal_weighted_same_interval
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t*Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {s t : ℝ≥0} (hst : s≤t) {w : Ω → ℝ}
    (hw : StronglyMeasurable[𝒢 s] w) (hwTop : MemLp w ⊤ μ) :
    (∫ ω,w ω*((X t ω-X s ω)*(Y t ω-Y s ω)) ∂μ)=0 := by
  let d := (X t-X s)*(Y t-Y s)
  have hd₁ : MemLp d 1 μ := ((hX₂ t).sub (hX₂ s)).mul ((hY₂ t).sub (hY₂ s))
  have hi : Integrable (w*d) μ := (hwTop.mul hd₁ : MemLp (w*d) 1 μ).integrable le_rfl
  have he := conditional_covariance_of_compensated_product hX hY (C := fun _ => 0)
    (by simpa only [sub_zero] using hXY) hX₂ hY₂ hst
  have he' : μ[d | 𝒢 s] =ᵐ[μ] 0 := by simpa only [d,sub_self,condExp_zero] using he
  have he₀ := (condExp_mul_of_stronglyMeasurable_left hw hi (hd₁.integrable le_rfl)).trans
    (EventuallyEq.rfl.mul he')
  calc
    _ = ∫ ω,μ[w*d | 𝒢 s] ω ∂μ := (integral_condExp (𝒢.le s)).symm
    _ = _ := by
      apply (integral_congr_ae he₀).trans
      simp

private theorem orthogonal_rect_ordered
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t*Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {s t u v : ℝ≥0} (hsu : s≤u) (huv : u≤v) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[𝒢 s] f) (hg : StronglyMeasurable[𝒢 u] g)
    (hfTop : MemLp f ⊤ μ) (hgTop : MemLp g ⊤ μ) :
    (∫ ω,(f ω*(X t ω-X s ω))*(g ω*(Y v ω-Y u ω)) ∂μ)=0 := by
  let w := f*g
  have hw : StronglyMeasurable[𝒢 u] w := (hf.mono (𝒢.mono hsu)).mul hg
  have hwTop : MemLp w ⊤ μ := hfTop.mul hgTop
  have hA (z : ℝ≥0) (hz : z≤u) :
      (∫ ω,w ω*((X z ω-X s ω)*(Y v ω-Y u ω)) ∂μ)=0 := by
    have hh : StronglyMeasurable[𝒢 u] (w*(X z-X s)) :=
      hw.mul (((hX.stronglyAdapted z).mono (𝒢.mono hz)).sub
        ((hX.stronglyAdapted s).mono (𝒢.mono hsu)))
    have hh₂ : MemLp (w*(X z-X s)) 2 μ := hwTop.mul ((hX₂ z).sub (hX₂ s))
    simpa only [Pi.mul_apply,Pi.sub_apply,mul_assoc] using
      orthogonal_weighted_increment_zero hY hY₂ huv hh hh₂
  have hI (a b c d : ℝ≥0) :
      Integrable (fun ω => w ω*((X b ω-X a ω)*(Y d ω-Y c ω))) μ := by
    have hP : MemLp ((X b-X a)*(Y d-Y c)) 1 μ := ((hX₂ b).sub (hX₂ a)).mul ((hY₂ d).sub (hY₂ c))
    exact (hwTop.mul hP : MemLp (w*((X b-X a)*(Y d-Y c))) 1 μ).integrable le_rfl
  have hW : (∫ ω,(f ω*(X t ω-X s ω))*(g ω*(Y v ω-Y u ω)) ∂μ)=
      ∫ ω,w ω*((X t ω-X s ω)*(Y v ω-Y u ω)) ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    change _=f ω*g ω*((X t ω-X s ω)*(Y v ω-Y u ω))
    ring
  rw [hW]
  by_cases htu : t≤u
  · exact hA t htu
  have hut : u≤t := (lt_of_not_ge htu).le
  have hsplit : (∫ ω,w ω*((X t ω-X s ω)*(Y v ω-Y u ω)) ∂μ)=
      (∫ ω,w ω*((X u ω-X s ω)*(Y v ω-Y u ω)) ∂μ) +
      ∫ ω,w ω*((X t ω-X u ω)*(Y v ω-Y u ω)) ∂μ := by
    rw [← integral_add (hI s u u v) (hI u t u v)]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by ring
  rw [hsplit,hA u le_rfl,zero_add]
  rcases le_total t v with htv|hvt
  · have hLate : (∫ ω,w ω*((X t ω-X u ω)*(Y v ω-Y t ω)) ∂μ)=0 := by
      have hWm : StronglyMeasurable[𝒢 t] (w*(X t-X u)) :=
        (hw.mono (𝒢.mono hut)).mul ((hX.stronglyAdapted t).sub ((hX.stronglyAdapted u).mono (𝒢.mono hut)))
      have hWp : MemLp (w*(X t-X u)) 2 μ := hwTop.mul ((hX₂ t).sub (hX₂ u))
      simpa only [Pi.mul_apply,Pi.sub_apply,mul_assoc] using
        orthogonal_weighted_increment_zero hY hY₂ htv hWm hWp
    have hCore := orthogonal_weighted_same_interval hX hY hXY hX₂ hY₂ hut hw hwTop
    calc
      _ = (∫ ω,w ω*((X t ω-X u ω)*(Y t ω-Y u ω)) ∂μ)+
          ∫ ω,w ω*((X t ω-X u ω)*(Y v ω-Y t ω)) ∂μ := by
        rw [← integral_add (hI u t u t) (hI u t t v)]
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by ring
      _ = _ := by rw [hCore,hLate,add_zero]
  · have hLate : (∫ ω,w ω*((X t ω-X v ω)*(Y v ω-Y u ω)) ∂μ)=0 := by
      have hWm : StronglyMeasurable[𝒢 v] (w*(Y v-Y u)) :=
        (hw.mono (𝒢.mono huv)).mul ((hY.stronglyAdapted v).sub ((hY.stronglyAdapted u).mono (𝒢.mono huv)))
      have hWp : MemLp (w*(Y v-Y u)) 2 μ := hwTop.mul ((hY₂ v).sub (hY₂ u))
      calc
        _ = ∫ ω,(w ω*(Y v ω-Y u ω))*(X t ω-X v ω) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun ω => by ring
        _ = _ := orthogonal_weighted_increment_zero hX hX₂ hvt hWm hWp
    have hCore := orthogonal_weighted_same_interval hX hY hXY hX₂ hY₂ huv hw hwTop
    calc
      _ = (∫ ω,w ω*((X v ω-X u ω)*(Y v ω-Y u ω)) ∂μ)+
          ∫ ω,w ω*((X t ω-X v ω)*(Y v ω-Y u ω)) ∂μ := by
        rw [← integral_add (hI u v u v) (hI v t u v)]
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by ring
      _ = _ := by rw [hCore,hLate,add_zero]

theorem orthogonal_joint_rect_increment
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t*Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    {s t u v : ℝ≥0} (hst : s≤t) (huv : u≤v) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[𝒢 s] f) (hg : StronglyMeasurable[𝒢 u] g)
    (hfTop : MemLp f ⊤ μ) (hgTop : MemLp g ⊤ μ) :
    (∫ ω,(f ω*(X t ω-X s ω))*(g ω*(Y v ω-Y u ω)) ∂μ)=0 := by
  rcases le_total s u with hsu|hus
  · exact orthogonal_rect_ordered hX hY hXY hX₂ hY₂ hsu huv hf hg hfTop hgTop
  · have hyx : Martingale (fun t => Y t*X t) 𝒢 μ := by simpa only [mul_comm] using hXY
    simpa only [mul_comm] using orthogonal_rect_ordered hY hX hyx hY₂ hX₂ hus hst hg hf hgTop hfTop

private theorem orthogonal_joint_simple_cross
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t*Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (V W : SimpleProcess ℝ 𝒢) :
    (∫ ω,jointItoSimple X V ω*jointItoSimple Y W ω ∂μ)=0 := by
  have hTop (F : SimpleProcess ℝ 𝒢) (p : ℝ≥0 × ℝ≥0) : MemLp (F.value p) ⊤ μ :=
    memLp_top_of_bound ((F.measurable_value p).mono (𝒢.le p.1) le_rfl).aestronglyMeasurable
      F.valueBound (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using F.value_le_valueBound p ω)
  have hi (p q : ℝ≥0 × ℝ≥0) :
      Integrable (fun ω => (V.value p ω*(X p.2 ω-X p.1 ω))*
        (W.value q ω*(Y q.2 ω-Y q.1 ω))) μ := by
    have hp : MemLp (V.value p*(X p.2-X p.1)) 2 μ := (hTop V p).mul ((hX₂ p.2).sub (hX₂ p.1))
    have hq : MemLp (W.value q*(Y q.2-Y q.1)) 2 μ := (hTop W q).mul ((hY₂ q.2).sub (hY₂ q.1))
    exact hp.integrable_mul hq
  simp only [jointItoSimple,Finsupp.sum,Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_eq_zero
  intro p hp
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_eq_zero
  intro q hq
  exact orthogonal_joint_rect_increment hX hY hXY hX₂ hY₂
    (V.le_of_mem_support_value p hp) (W.le_of_mem_support_value q hq)
    (V.measurable_value p).stronglyMeasurable (W.measurable_value q).stronglyMeasurable (hTop V p) (hTop W q)

private theorem mixedRealLpInner {f g : Lp ℝ 2 μ} :
    ⟪f,g⟫_ℝ = ∫ ω,f ω*g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => mul_comm _ _

/-- The paired stochastic integrals can use different predictable
weights. Extending shorter integrands by zero includes mixed times. -/
theorem orthogonal_jointItoIntegralCLM_cross (T : ℝ≥0)
    (hX : Martingale X 𝒢 μ) (hY : Martingale Y 𝒢 μ)
    (hXY : Martingale (fun t => X t*Y t) 𝒢 μ)
    (hX₂ : ∀ t, MemLp (X t) 2 μ) (hY₂ : ∀ t, MemLp (Y t) 2 μ)
    (hXclock : Martingale (fun t ω => X t ω^2-((min t T:ℝ≥0):ℝ)) 𝒢 μ)
    (hYclock : Martingale (fun t ω => Y t ω^2-((min t T:ℝ≥0):ℝ)) 𝒢 μ)
    (f g : Lp ℝ 2 (jointPredictableMeasure 𝒢 μ T)) :
    (∫ ω,jointItoIntegralCLM T hX₂ f ω*jointItoIntegralCLM T hY₂ g ω ∂μ)=0 := by
  rw [← mixedRealLpInner]
  let IX := jointItoIntegralCLM (𝒢 := 𝒢) T hX₂
  let IY := jointItoIntegralCLM (𝒢 := 𝒢) T hY₂
  change ⟪IX f,IY g⟫_ℝ=0
  have hd := jointSimpleAssembly_denseRange (μ := μ) T 𝒢
  refine DenseRange.induction_on hd (p := fun u => ⟪IX u,IY g⟫_ℝ=0) f
    (isClosed_eq (IX.continuous.inner continuous_const) continuous_const) ?_
  intro V
  refine DenseRange.induction_on hd (p := fun u => ⟪IX (jointSimpleAssembly T 𝒢 V),IY u⟫_ℝ=0) g
    (isClosed_eq (continuous_const.inner IY.continuous) continuous_const) ?_
  intro W
  dsimp only [IX,IY]
  rw [jointItoIntegralCLM_agrees T hX₂ hX hXclock,jointItoIntegralCLM_agrees T hY₂ hY hYclock,
    mixedRealLpInner]
  refine (integral_congr_ae ?_).trans (orthogonal_joint_simple_cross hX hY hXY hX₂ hY₂ V.val W.val)
  exact (memLp_jointItoSimple hX₂ V.val).coeFn_toLp.mul (memLp_jointItoSimple hY₂ W.val).coeFn_toLp

#print axioms orthogonal_jointItoIntegralCLM_cross

end RoughHeston
