package cn.ac.ios.Bean;

import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class SmtNode{
    private List<String> intersectionRegexes;
    private SmtNode next;

    public SmtNode(List<String> intersectionRegexes, SmtNode next) {
        this.intersectionRegexes = intersectionRegexes;
        this.next = next;
    }

    public SmtNode(List<String> intersectionRegexes) {
        this.intersectionRegexes = intersectionRegexes;
        this.next = null;
    }

    public SmtNode(SmtNode smtNode) {
        this.intersectionRegexes = new ArrayList<>(smtNode.intersectionRegexes);
        this.next = smtNode.next;
    }

    public List<String> getIntersectionRegexes() {
        return intersectionRegexes;
    }

    public SmtNode appendNode(SmtNode node) {
        if (this.next == null) {
            this.next = node;
        } else {
            SmtNode temp = this.next;
            while (temp.next != null) {
                temp = temp.next;
            }
            temp.next = node;
        }
        return this;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("SmtNode{");
        sb.append("intersectionRegexes=").append(intersectionRegexes);
        if (next != null) {
            sb.append(", next=").append(next);
        }
        sb.append('}');
        return sb.toString();
    }

    public ArrayList<Pair<String, ArrayList<String>>> toSmtLib() throws TranslationException, FormatNotAvailableException {
        ArrayList<Pair<String, ArrayList<String>>> result = new ArrayList<>();

        StringBuilder sb = new StringBuilder();
        ArrayList<String> sbRegexes = new ArrayList<>();

        // 如果当前正则数组为1，直接生成正则对应的SMT-LIB表达式
        if (intersectionRegexes.size() == 1) {
            ;
        } else {
            // 如果当前正则数组大于1，生成交集表达式
            // sb.append("(re.inter ");
            ArrayList<String> smtlibForSingleRegexes = new ArrayList<>();
            for (String regex : intersectionRegexes) {
                if (regex.contains("＆") || regex.contains("～")) {
                    return new ArrayList<>();
                }
                String regexsmt = Translator.INSTANCE.translate("cvc4", regex);
                // String regexsmt = getSMTLIB(regex);
                // 如果regexsmt中含有"re.inter"，return new ArrayList<>();
                // if (regexsmt.contains("re.inter") || regexsmt.contains("re.comp")) {
                //     return new ArrayList<>();
                // }

                // sb.append(regexsmt).append(" ");

                smtlibForSingleRegexes.add(regexsmt);
            }
            // sb.append(")");
            int nonEmptyCount = 0;
            for (String regex : smtlibForSingleRegexes) {
                if (!regex.equals("")) {
                    nonEmptyCount++;
                }
            }
            if (nonEmptyCount == 0) {
                return new ArrayList<>();
            }
            else if (nonEmptyCount == 1) {
                smtlibForSingleRegexes.add("(str.to.re \"\")");
            }

            sb.append("(re.inter ");
            for (String regex : smtlibForSingleRegexes) {
                if (!regex.equals("")) {
                    sb.append(regex).append(" ");
                }
            }
            sb.append(")");

            sbRegexes.addAll(intersectionRegexes);

            result.add(new Pair<>(sb.toString(), sbRegexes));
        }

        if (next != null) {
            ArrayList<Pair<String, ArrayList<String>>> nextStrings = next.toSmtLib();
            result.addAll(nextStrings);
        }

        return result;
    }


    public static String getSMTLIB(String regex) {
        String result = "";
        try {
            // 创建并启动进程
            ProcessBuilder processBuilder = new ProcessBuilder("./IntersectionK");
            processBuilder.redirectErrorStream(true); // 将错误输出和标准输出合并
            Process process = processBuilder.start();

            // 通过进程的输出流向其标准输入写入数据
            BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
            writer.write(regex);
            writer.newLine();
            writer.flush();
            writer.close(); // 完成写入后需要关闭流

            // 读取进程的输出
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                // System.out.println(line);
                result += line;
            }
            reader.close();


            // 等待进程结束
            int exitCode = process.waitFor();
            // System.out.println("Exited with code: " + exitCode);
            // 如果进程错误退出，抛出异常
            if (exitCode != 0) {
                throw new RuntimeException("Process exited with error code " + exitCode);
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        return result;
    }

}
