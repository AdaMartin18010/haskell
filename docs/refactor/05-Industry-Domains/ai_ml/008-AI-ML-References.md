# AI/ML参考资料

## 1. 学术论文

### 1.1 机器学习基础

1. "Pattern Recognition and Machine Learning", Bishop, 2006
2. "The Elements of Statistical Learning", Hastie et al., 2009
3. "Deep Learning", Goodfellow et al., 2016
4. "Reinforcement Learning: An Introduction", Sutton & Barto, 2018

### 1.2 深度学习

1. "Attention Is All You Need", Vaswani et al., NeurIPS 2017
2. "BERT: Pre-training of Deep Bidirectional Transformers", Devlin et al., NAACL 2019
3. "Generative Adversarial Networks", Goodfellow et al., NeurIPS 2014
4. "Denoising Diffusion Probabilistic Models", Ho et al., NeurIPS 2020

### 1.3 形式化方法

1. "Formal Methods in Machine Learning", ACM Computing Surveys, 2024
2. "Verification of Neural Networks", CAV 2023
3. "Fairness in Machine Learning", FAccT 2023
4. "Robustness Verification", ICML 2023

## 2. 技术标准

### 2.1 AI标准

- ISO/IEC 23053:2022 Framework for Artificial Intelligence (AI) System Using Machine Learning (ML)
- IEEE 2857:2021 Privacy Engineering for System Lifecycle Processes
- IEEE 7000:2021 Model Process for Addressing Ethical Concerns During System Design
- ISO/IEC 42001:2023 Information technology — Artificial intelligence — Management system

### 2.2 数据标准

- ISO/IEC 27001:2013 Information security management systems
- GDPR: General Data Protection Regulation
- CCPA: California Consumer Privacy Act
- HIPAA: Health Insurance Portability and Accountability Act

## 3. 开源项目

### 3.1 Haskell项目

```haskell
-- 项目索引
data MLProject = MLProject
  { name :: String
  , url :: String
  , description :: String
  , category :: Category
  }

projects :: [MLProject]
projects =
  [ MLProject
      { name = "hasktorch"
      , url = "https://github.com/hasktorch/hasktorch"
      , description = "Haskell bindings for PyTorch"
      , category = DeepLearning
      }
  , MLProject
      { name = "grenade"
      , url = "https://github.com/HuwCampbell/grenade"
      , description = "Deep learning library"
      , category = DeepLearning
      }
  , MLProject
      { name = "formal-ml"
      , url = "https://github.com/formal-ml"
      , description = "Formal methods for ML"
      , category = FormalMethods
      }
  ]
```

### 3.2 Rust项目

```rust
// 项目索引
pub struct RustMLProject {
    pub name: String,
    pub url: String,
    pub description: String,
    pub category: Category,
}

pub fn get_projects() -> Vec<RustMLProject> {
    vec![
        RustMLProject {
            name: "burn".to_string(),
            url: "https://github.com/burn-rs/burn".to_string(),
            description: "Flexible and comprehensive Deep Learning Framework".to_string(),
            category: Category::DeepLearning,
        },
        RustMLProject {
            name: "tch-rs".to_string(),
            url: "https://github.com/LaurentMazare/tch-rs".to_string(),
            description: "Rust bindings for PyTorch".to_string(),
            category: Category::DeepLearning,
        },
        RustMLProject {
            name: "rust-ml".to_string(),
            url = "https://github.com/rust-ml".to_string(),
            description: "Machine learning ecosystem".to_string(),
            category: Category::MachineLearning,
        },
    ]
}
```

### 3.3 形式化工具

- [Formal ML](https://github.com/formal-ml)
- [ML Verification](https://github.com/ml-verify)
- [AI Safety](https://github.com/ai-safety)
- [Fairness ML](https://github.com/fairness-ml)

## 4. 工具与框架

### 4.1 深度学习框架

1. 主流框架
   - TensorFlow
   - PyTorch
   - JAX
   - MXNet

2. 专业框架
   - Hugging Face Transformers
   - FastAI
   - Keras
   - ONNX

### 4.2 机器学习库

1. 传统ML
   - Scikit-learn
   - XGBoost
   - LightGBM
   - CatBoost

2. 强化学习
   - Stable Baselines3
   - RLlib
   - OpenAI Gym
   - Unity ML-Agents

## 5. 在线资源

### 5.1 学习平台

1. MOOC课程
   - Coursera: Machine Learning (Andrew Ng)
   - edX: Deep Learning Fundamentals
   - Udacity: Deep Learning Nanodegree
   - MIT OCW: Introduction to Machine Learning

2. 专业认证
   - Google TensorFlow Developer Certificate
   - AWS Machine Learning Specialty
   - Microsoft Azure AI Engineer
   - IBM AI Engineering Professional

### 5.2 技术社区

1. AI/ML社区
   - [Papers With Code](https://paperswithcode.com)
   - [arXiv](https://arxiv.org)
   - [Distill](https://distill.pub)
   - [Towards Data Science](https://towardsdatascience.com)

2. 形式化方法社区
   - [Formal Methods in ML](https://formal-ml.org)
   - [AI Safety](https://ai-safety.org)
   - [ML Fairness](https://ml-fairness.org)

## 6. 会议与期刊

### 6.1 学术会议

1. 机器学习会议
   - ICML: International Conference on Machine Learning
   - NeurIPS: Neural Information Processing Systems
   - ICLR: International Conference on Learning Representations
   - AAAI: Association for the Advancement of Artificial Intelligence

2. 形式化方法会议
   - FM: International Symposium on Formal Methods
   - CAV: Computer Aided Verification
   - TACAS: Tools and Algorithms for the Construction and Analysis of Systems

### 6.2 学术期刊

1. AI/ML期刊
   - Journal of Machine Learning Research (JMLR)
   - IEEE Transactions on Pattern Analysis and Machine Intelligence (TPAMI)
   - Artificial Intelligence
   - Machine Learning

2. 形式化方法期刊
   - Formal Methods in System Design
   - Journal of Automated Reasoning
   - Formal Aspects of Computing

## 7. 研究机构

### 7.1 学术机构

1. 研究实验室
   - MIT CSAIL
   - Stanford AI Lab
   - Berkeley AI Research
   - CMU Machine Learning Department

2. 研究中心
   - OpenAI
   - DeepMind
   - Anthropic
   - Microsoft Research

### 7.2 产业机构

1. 企业研究院
   - Google AI
   - Facebook AI Research
   - Amazon AI
   - Apple Machine Learning

2. 标准组织
   - IEEE AI Standards Committee
   - ISO/IEC JTC 1/SC 42
   - NIST AI Risk Management Framework

## 8. 相关链接

### 8.1 资源导航

- [AI Resources](https://ai-resources.org)
- [ML Tools](https://ml-tools.org)
- [Formal Methods Index](https://formal-methods.org)

### 8.2 社区链接

- [AI Forum](https://ai-forum.org)
- [ML Community](https://ml-community.org)
- [AI Safety Network](https://ai-safety.org)

## 9. 交叉引用

参见本知识库其他相关文档：

- [应用案例](004-AI-ML-Case-Studies.md)
- [最佳实践](005-AI-ML-Best-Practices.md)
- [形式化建模](006-AI-ML-Formal-Modeling.md)
- [趋势展望](007-AI-ML-Trends.md)
