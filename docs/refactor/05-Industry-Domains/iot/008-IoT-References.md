# IoT参考资料

## 1. 学术论文

### 1.1 形式化方法

1. "Formal Methods in IoT: A Comprehensive Survey", ACM Computing Surveys, 2024
2. "Type-Safe IoT Systems", PLDI 2023
3. "Automated Verification of IoT Protocols", CAV 2023
4. "Real-Time Systems in IoT", Real-Time Systems Journal, 2024

### 1.2 IoT系统

1. "Edge Computing in IoT: Formal Foundations", IEEE IoT Journal, 2024
2. "AI-Driven IoT Systems", ACM IoT 2023
3. "Security in IoT Networks", NDSS 2023
4. "Energy-Efficient IoT Protocols", IEEE Transactions on IoT, 2024

## 2. 技术标准

### 2.1 IoT标准

- IEEE 802.15.4: Low-Rate Wireless Personal Area Networks
- IEEE 802.11ah: WiFi for IoT
- 3GPP Release 17: Cellular IoT
- ISO/IEC 30141:2018 Internet of Things Reference Architecture

### 2.2 通信协议

- MQTT 5.0: Message Queuing Telemetry Transport
- CoAP: Constrained Application Protocol
- LoRaWAN 1.1: Long Range Wide Area Network
- Zigbee 3.0: Low-Power Wireless Network

## 3. 开源项目

### 3.1 Haskell项目

```haskell
-- 项目索引
data IoTProject = IoTProject
  { name :: String
  , url :: String
  , description :: String
  , category :: Category
  }

projects :: [IoTProject]
projects =
  [ IoTProject
      { name = "iot-verify"
      , url = "https://github.com/iot-verify"
      , description = "IoT system verification framework"
      , category = FormalMethods
      }
  , IoTProject
      { name = "edge-compute"
      , url = "https://github.com/edge-compute"
      , description = "Edge computing platform"
      , category = EdgeComputing
      }
  ]
```

### 3.2 Rust项目

```rust
// 项目索引
pub struct RustIoTProject {
    pub name: String,
    pub url: String,
    pub description: String,
    pub category: Category,
}

pub fn get_projects() -> Vec<RustIoTProject> {
    vec![
        RustIoTProject {
            name: "iot-platform".to_string(),
            url: "https://github.com/iot-platform".to_string(),
            description: "High-performance IoT platform".to_string(),
            category: Category::Platform,
        },
        RustIoTProject {
            name: "edge-ai".to_string(),
            url: "https://github.com/edge-ai".to_string(),
            description: "Edge AI framework".to_string(),
            category: Category::AI,
        },
    ]
}
```

### 3.3 形式化工具

- [TLA+ IoT](https://github.com/tlaplus-iot)
- [Coq IoT](https://github.com/coq-iot)
- [Formal IoT](https://github.com/formal-iot)
- [IoT Verify](https://github.com/iot-verify)

## 4. 工具与框架

### 4.1 开发工具

1. IoT平台
   - AWS IoT Core
   - Azure IoT Hub
   - Google Cloud IoT
   - IBM Watson IoT

2. 边缘计算
   - EdgeX Foundry
   - KubeEdge
   - OpenYurt
   - Baetyl

### 4.2 仿真工具

1. 网络仿真
   - NS-3
   - OMNeT++
   - Cooja
   - WSNet

2. 设备仿真
   - IoT Device Simulator
   - Device Simulator Express
   - IoT Simulator
   - Virtual IoT Device

## 5. 在线资源

### 5.1 学习平台

1. MOOC课程
   - Coursera: Internet of Things
   - edX: IoT Systems
   - Udacity: IoT Programming
   - MIT OCW: IoT Technology

2. 专业认证
   - AWS IoT Certification
   - Azure IoT Developer
   - Google Cloud IoT
   - Cisco IoT

### 5.2 技术社区

1. IoT社区
   - [IoT World](https://www.iotworld.com)
   - [IoT For All](https://www.iotforall.com)
   - [IoT Central](https://www.iotcentral.io)
   - [IoT Tech News](https://www.iottechnews.com)

2. 形式化方法社区
   - [Formal Methods in IoT](https://formal-iot.org)
   - [TLA+ Community](https://tlaplus.community)
   - [Coq Users](https://coq-club.org)

## 6. 会议与期刊

### 6.1 学术会议

1. IoT会议
   - IoTDI: IEEE International Conference on Internet of Things Design and Implementation
   - IoT: IEEE World Forum on Internet of Things
   - IoT-Sys: Workshop on Internet of Things Systems

2. 形式化方法会议
   - FM: International Symposium on Formal Methods
   - CAV: Computer Aided Verification
   - TACAS: Tools and Algorithms for the Construction and Analysis of Systems

### 6.2 学术期刊

1. IoT期刊
   - IEEE Internet of Things Journal
   - ACM Transactions on Internet of Things
   - Internet of Things
   - IoT Journal

2. 形式化方法期刊
   - Formal Methods in System Design
   - Journal of Automated Reasoning
   - Formal Aspects of Computing

## 7. 研究机构

### 7.1 学术机构

1. 研究实验室
   - MIT IoT Lab
   - Stanford IoT Research
   - Berkeley IoT Group
   - CMU IoT Institute

2. 研究中心
   - IoT Research Center
   - Formal Methods Research Center
   - Edge Computing Laboratory

### 7.2 产业机构

1. 企业研究院
   - Microsoft IoT Research
   - Google IoT Research
   - IBM IoT Research

2. 标准组织
   - IEEE IoT Initiative
   - ISO/IEC JTC 1/SC 41
   - IETF IoT Working Group

## 8. 相关链接

### 8.1 资源导航

- [IoT Resources](https://iot-resources.org)
- [Formal Methods Tools](https://formal-tools.org)
- [Edge Computing Index](https://edge-computing.org)

### 8.2 社区链接

- [IoT Tech Forum](https://iot-forum.org)
- [Formal IoT Community](https://formal-iot.org)
- [Edge Computing Network](https://edge-network.org)

## 9. 交叉引用

参见本知识库其他相关文档：

- [应用案例](004-IoT-Case-Studies.md)
- [最佳实践](005-IoT-Best-Practices.md)
- [形式化建模](006-IoT-Formal-Modeling.md)
- [趋势展望](007-IoT-Trends.md)
