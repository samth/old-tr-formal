#cs
(module main mzscheme
  (require (lib "cmdline.ss"))
  (require (lib "etc.ss"))
  (require "lang/to-string.ss")
  (require "semantic/semantic-analysis.ss")
  (require "syntactic/syntactic-analysis.ss")
  (require "config.ss")

  ;; command-line:   #("-s" "C:/Documents and Settings/dherman/My Documents/NASA/test/in-source" "-t" "C:/Documents and Settings/dherman/My Documents/NASA/test/out-source")

  (define *target* #f)

  (command-line "trinity" (current-command-line-arguments)
    (once-each
     [("-c" "--classpath")
      classpath
      "Set the classpath."
      (current-classpath (path-list-string->path-list classpath null))]
     [("-s" "--sourcepath")
      sourcepath
      "Set the sourcepath."
      (current-sourcepath (path-list-string->path-list sourcepath null))]
     [("-t" "--target")
      target
      "Sets the target directory."
      (set! *target* target)])
    (args rulefiles
      (current-rules rulefiles)))

  (unless *target*
    (error 'trinity "no target directory specified"))
  (when (null? (current-sourcepath))
    (error 'trinity "no sourcepath specified"))

  (printf "CLASSPATH: ~v~n" (current-classpath))
  (printf "SOURCEPATH: ~v~n" (current-sourcepath))

  (wrap-current-display-handlers!)

  (define asts   (time (syntactic-analysis (current-sourcepath))))
  ;(printf "asts: ~v~n" asts)
  (define types  (time (semantic-analysis asts)))

  (provide))
