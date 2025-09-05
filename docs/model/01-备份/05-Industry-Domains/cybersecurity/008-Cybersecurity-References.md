# 网络安全参考资料

## 1. 学术论文

### 1.1 形式化方法

1. "Formal Methods in Cybersecurity: A Comprehensive Survey", ACM Computing Surveys, 2024
2. "Type-Safe Security Protocols", PLDI 2023
3. "Automated Verification of Security Properties", CAV 2023
4. "Quantum Methods in Cybersecurity", Nature Cybersecurity, 2024

### 1.2 安全系统

1. "Zero Trust Architecture: Formal Foundations", IEEE Security & Privacy, 2024
2. "AI-Driven Security Systems", ACM CCS 2023
3. "Blockchain Security Verification", NDSS 2023
4. "IoT Security Formalization", USENIX Security 2024

## 2. 技术标准

### 2.1 安全标准

- ISO/IEC 27001:2024 Information Security Management
- ISO/IEC 27002:2024 Information Security Controls
- NIST Cybersecurity Framework 2.0
- NIST Zero Trust Architecture

### 2.2 密码学标准

- FIPS 140-3 Cryptographic Module Validation
- NIST Post-Quantum Cryptography Standards
- RFC 8446 TLS 1.3
- RFC 5246 TLS 1.2

## 3. 开源项目

### 3.1 Haskell项目

```haskell
-- 项目索引
data SecurityProject = SecurityProject
  { name :: String
  , url :: String
  , description :: String
  , category :: Category
  }

projects :: [SecurityProject]
projects =
  [ SecurityProject
      { name = "crypto-verify"
      , url = "https://github.com/crypto-verify"
      , description = "Cryptographic protocol verification"
      , category = FormalMethods
      }
  , SecurityProject
      { name = "zero-trust"
      , url = "https://github.com/zero-trust"
      , description = "Zero trust architecture implementation"
      , category = Architecture
      }
  ]
```

### 3.2 Rust项目

```rust
// 项目索引
pub struct RustSecurityProject {
    pub name: String,
    pub url: String,
    pub description: String,
    pub category: Category,
}

pub fn get_projects() -> Vec<RustSecurityProject> {
    vec![
        RustSecurityProject {
            name: "security-framework".to_string(),
            url: "https://github.com/security-framework".to_string(),
            description: "High-performance security framework".to_string(),
            category: Category::Framework,
        },
        RustSecurityProject {
            name: "threat-detection".to_string(),
            url: "https://github.com/threat-detection".to_string(),
            description: "AI-powered threat detection".to_string(),
            category: Category::AI,
        },
    ]
}
```

### 3.3 形式化工具

- [TLA+ Security](https://github.com/tlaplus-security)
- [Coq Security](https://github.com/coq-security)
- [Formal Security](https://github.com/formal-security)
- [Security Verify](https://github.com/security-verify)

## 4. 工具与框架

### 4.1 安全工具

1. 渗透测试工具
   - Metasploit
   - Nmap
   - Wireshark
   - Burp Suite

2. 漏洞扫描工具
   - Nessus
   - OpenVAS
   - Qualys
   - Rapid7

### 4.2 形式化工具

1. 协议验证
   - ProVerif
   - Tamarin
   - CryptoVerif
   - EasyCrypt

2. 模型检验
   - SPIN
   - UPPAAL
   - PRISM
   - NuSMV

## 5. 在线资源

### 5.1 学习平台

1. MOOC课程
   - Coursera: Cybersecurity
   - edX: Network Security
   - Udacity: Security Engineering
   - MIT OCW: Computer Security

2. 专业认证
   - CISSP
   - CEH
   - CompTIA Security+
   - SANS GIAC

### 5.2 技术社区

1. 安全社区
   - [OWASP](https://owasp.org)
   - [SANS](https://www.sans.org)
   - [Black Hat](https://www.blackhat.com)
   - [DEF CON](https://defcon.org)

2. 形式化方法社区
   - [Formal Methods in Security](https://formal-security.org)
   - [TLA+ Community](https://tlaplus.community)
   - [Coq Users](https://coq-club.org)

## 6. 会议与期刊

### 6.1 学术会议

1. 安全会议
   - CCS: ACM Conference on Computer and Communications Security
   - S&P: IEEE Symposium on Security and Privacy
   - NDSS: Network and Distributed System Security Symposium
   - USENIX Security: USENIX Security Symposium

2. 形式化方法会议
   - FM: International Symposium on Formal Methods
   - CAV: Computer Aided Verification
   - TACAS: Tools and Algorithms for the Construction and Analysis of Systems

### 6.2 学术期刊

1. 安全期刊
   - IEEE Security & Privacy
   - ACM Transactions on Information and System Security
   - Journal of Computer Security
   - Computers & Security

2. 形式化方法期刊
   - Formal Methods in System Design
   - Journal of Automated Reasoning
   - Formal Aspects of Computing

## 7. 研究机构

### 7.1 学术机构

1. 研究实验室
   - MIT CSAIL Security
   - Stanford Security Lab
   - Berkeley Security Group
   - CMU CyLab

2. 研究中心
   - Cybersecurity Research Center
   - Formal Methods Research Center
   - Cryptography Research Laboratory

### 7.2 产业机构

1. 企业研究院
   - Microsoft Security Research
   - Google Security Research
   - IBM Security Research

2. 标准组织
   - NIST Cybersecurity
   - ISO/IEC JTC 1/SC 27
   - IETF Security Area

## 8. 相关链接

### 8.1 资源导航

- [Cybersecurity Resources](https://cyber-resources.org)
- [Formal Methods Tools](https://formal-tools.org)
- [Security Standards Index](https://security-standards.org)

### 8.2 社区链接

- [Security Tech Forum](https://security-forum.org)
- [Formal Security Community](https://formal-security.org)
- [Security Architecture Network](https://security-arch.org)

## 9. 交叉引用

参见本知识库其他相关文档：

- [应用案例](004-Cybersecurity-Case-Studies.md)
- [最佳实践](005-Cybersecurity-Best-Practices.md)
- [形式化建模](006-Cybersecurity-Formal-Modeling.md)
- [趋势展望](007-Cybersecurity-Trends.md)
